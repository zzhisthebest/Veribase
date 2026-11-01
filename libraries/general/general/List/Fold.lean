import Mathlib
import general.List.ExtremumSelection
import general.List.Sequences
import general.List.Filter
import general.List.Transformations

namespace List

/-! # Generic foldl lemmas with monotone step functions

This module provides generic lemmas about `List.foldl` with a `Nat` accumulator
and an arbitrary step function `step : Nat → α → Nat`, with monotonicity and
boundedness hypotheses.

We also define `maxStep` and `minStep` — convenient step functions that fold
`max` or `min` of a projection, and prove specialized correctness lemmas for them.

Finally, we formalize double-folding over all ordered pairs in a list: computing
the maximum or minimum of a binary function `f d₁ d₂` over all `d₁, d₂ ∈ xs`.
-/

/-! ### Step functions for max/min folding with a projection -/

/-- Step function for maximum folding: returns the larger of `acc` and `f x`.
This is the step function used to compute `max {f x | x ∈ xs}` via `foldl`. -/
def maxStep {α : Type} (f : α → Nat) (acc : Nat) (x : α) : Nat :=
  if f x > acc then f x else acc

/-- Step function for minimum folding: returns the smaller of `acc` and `f x`.
This is the step function used to compute `min {f x | x ∈ xs}` via `foldl`. -/
def minStep {α : Type} (f : α → Nat) (acc : Nat) (x : α) : Nat :=
  if f x < acc then f x else acc

/-! ### Basic properties of `maxStep` and `minStep` -/

/-- `maxStep` is non-decreasing: `acc ≤ maxStep f acc x`. -/
lemma maxStep_ge_acc {α : Type} {f : α → Nat} {acc : Nat} {x : α} : acc ≤ maxStep f acc x := by
  dsimp [maxStep]
  split
  · exact Nat.le_of_lt (by assumption)
  · rfl

/-- `maxStep` is ≥ the function value: `f x ≤ maxStep f acc x`. -/
lemma maxStep_ge_val {α : Type} {f : α → Nat} {acc : Nat} {x : α} : f x ≤ maxStep f acc x := by
  dsimp [maxStep]
  split
  · rfl
  · exact Nat.le_of_not_gt (by assumption)

/-- `minStep` is non-increasing: `minStep f acc x ≤ acc`. -/
lemma minStep_le_acc {α : Type} {f : α → Nat} {acc : Nat} {x : α} : minStep f acc x ≤ acc := by
  dsimp [minStep]
  split
  · exact Nat.le_of_lt (by assumption)
  · rfl

/-- `minStep` is ≤ the function value: `minStep f acc x ≤ f x`. -/
lemma minStep_le_val {α : Type} {f : α → Nat} {acc : Nat} {x : α} : minStep f acc x ≤ f x := by
  dsimp [minStep]
  split
  · rfl
  · exact Nat.le_of_not_gt (by assumption)

/-- `maxStep` is monotone in the accumulator. -/
lemma maxStep_mono {α : Type} {f : α → Nat} {a₁ a₂ : Nat} {x : α} (h : a₁ ≤ a₂) :
    maxStep f a₁ x ≤ maxStep f a₂ x := by
  dsimp [maxStep]
  split
  · next h₁ =>
    split
    · rfl
    · omega
  · next h₁ =>
    split
    · omega
    · exact h

/-- `minStep` is monotone in the accumulator. -/
lemma minStep_mono {α : Type} {f : α → Nat} {a₁ a₂ : Nat} {x : α} (h : a₁ ≤ a₂) :
    minStep f a₁ x ≤ minStep f a₂ x := by
  dsimp [minStep]
  split
  · next h₁ =>
    split
    · rfl
    · omega
  · next h₁ =>
    split
    · omega
    · exact h

/-! ### Generic foldl lemmas -/

/-- If `P` holds for the initial accumulator `b`, and `f` preserves `P` on every step
(i.e., `P b` implies `P (f b a)` for all `a`), then `P` holds after folding `f` over `as`.
This is the primary induction lemma for proving invariants of `List.foldl`. -/
lemma foldl_preserves_invariant {α β : Type} (f : β → α → β) (P : β → Prop)
    (h_step : ∀ (b : β) (a : α), P b → P (f b a))
    (as : List α) (b : β) (h_init : P b) : P (as.foldl f b) := by
  induction' as with a as ih generalizing b
  · exact h_init
  · have h_b' : P (f b a) := h_step b a h_init
    simp [List.foldl]
    exact ih (f b a) h_b'

/-- If a binary operation `f` preserves property `P` on both arguments, and all elements
of list `s` satisfy `P`, then `foldl f init s` satisfies `P` provided `init` does.
This is a stronger version of `foldl_preserves_invariant` for the common case where
accumulator and list elements have the same type. -/
lemma foldl_preserves {α : Type} {f : α → α → α} {P : α → Prop}
    (h_preserve : ∀ a b, P a → P b → P (f a b)) (init : α) (h_init : P init)
    {s : List α} (h : ∀ x ∈ s, P x) : P (List.foldl f init s) := by
  have h_general : ∀ acc, P acc → P (List.foldl f acc s) := by
    revert h
    refine List.rec ?_ ?_ s
    · intro h acc hacc
      simpa
    · intro x xs ih h acc hacc
      have hx : P x := h x (by simp)
      have hxs : ∀ y ∈ xs, P y := by
        intro y hy
        exact h y (by simp [hy])
      simp [List.foldl]
      exact ih hxs (f acc x) (h_preserve acc x hacc hx)
  exact h_general init h_init

/-- A fold preserves a `Pairwise` relation when the step function preserves it.
The step function `f` transforms a `stack : List α` given an element `x : β`, and if
`f` preserves `List.Pairwise R`, then `foldl f stack xs` also satisfies `List.Pairwise R`. -/
lemma foldl_preserves_pairwise {α β : Type} (f : List α → β → List α) (R : α → α → Prop)
    (h_preserve : ∀ (stack : List α) (x : β), List.Pairwise R stack → List.Pairwise R (f stack x))
    (xs : List β) (stack : List α) (h : List.Pairwise R stack) :
    List.Pairwise R (List.foldl f stack xs) := by
  induction xs generalizing stack with
  | nil => simp [List.foldl, h]
  | cons y ys ih =>
    simp [List.foldl]
    apply ih
    exact h_preserve stack y h

/-! ### `Nodup` preservation through `foldl` -/

/-- If a step function maps nodup lists to nodup lists, its `foldl` also maps nodup to nodup.
This is a general induction principle for proving that foldl-based algorithms — such as
deduplication, set union, or merge — produce nodup results from a nodup initial accumulator.

For example, if `f acc x` preserves `List.Nodup acc`, then `xs.foldl f acc` is nodup
whenever `acc` is. -/
lemma nodup_foldl_of_step_nodup {α β : Type} (f : List α → β → List α)
    (h_step : ∀ (acc : List α) (x : β), List.Nodup acc → List.Nodup (f acc x))
    (xs : List β) (acc : List α) (h_acc : List.Nodup acc) : List.Nodup (xs.foldl f acc) := by
  induction' xs with x xs ih generalizing acc
  · exact h_acc
  · rw [List.foldl]
    apply ih
    exact h_step acc x h_acc

/-- A fold preserves a length bound: if each step adds at most one element
(i.e., `(f stack x).length ≤ stack.length + 1`), then the total fold length is
bounded by `xs.length + stack.length`. -/
lemma foldl_length_bound {α β : Type} (f : List α → β → List α)
    (h_bound : ∀ (stack : List α) (x : β), (f stack x).length ≤ stack.length + 1)
    (xs : List β) (stack : List α) : (List.foldl f stack xs).length ≤ xs.length + stack.length := by
  induction xs generalizing stack with
  | nil => simp [List.foldl]
  | cons y ys ih =>
    simp [List.foldl]
    have h_merge : (f stack y).length ≤ stack.length + 1 := h_bound stack y
    have h_ih := ih (f stack y)
    omega

/-- If each step of a `foldl` adds at most `M` to the accumulator
(i.e., `f acc x ≤ acc + M`), then the fold result is bounded by
`init + L.length * M`. -/
lemma foldl_add_bound {α : Type} (f : Nat → α → Nat) (M init : Nat) (L : List α)
    (h : ∀ acc x, f acc x ≤ acc + M) : L.foldl f init ≤ init + L.length * M := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp
    have hx : f init x ≤ init + M := h init x
    have hxs : xs.foldl f (f init x) ≤ f init x + xs.length * M := ih (f init x)
    apply le_trans hxs
    have h_simp : init + (xs.length + 1) * M = (init + M) + xs.length * M := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [h_simp]
    exact Nat.add_le_add_right hx (xs.length * M)

/-- If the step function is non-decreasing in the accumulator
(i.e., `a ≤ step a i` for all `a` and `i`), then `init ≤ foldl step init xs`.
This holds for any `Preorder β`, not just `Nat`.
This is the dual of `foldl_le_init`. -/
lemma foldl_ge_init {α β : Type} [Preorder β] {step : β → α → β}
    (h_nondec : ∀ (acc : β) (x : α), acc ≤ step acc x) {init : β} {xs : List α} :
    init ≤ List.foldl step init xs := by
  induction' xs with x xs ih generalizing init
  · exact le_refl init
  · simp
    have h0 : init ≤ step init x := h_nondec init x
    have h1 : step init x ≤ List.foldl step (step init x) xs := ih (init := step init x)
    exact le_trans h0 h1

/-- If `b` is bounded above by `F init' x` for *all* values of `init'` (not just the current
accumulator), and `F` is expansive (`acc ≤ F acc x`), then `b ≤ l.foldl F init` whenever `x ∈ l`.

The key insight is that `b` is constant — it does not depend on `init`. This makes the
induction hypothesis directly coincide with the goal, avoiding the need for a monotonicity
hypothesis on `F`. Contrast with `foldl_ge_mem_step` which requires both expansiveness and
monotonicity but proves `step init x ≤ foldl` (a conclusion that depends on `init`). -/
lemma const_le_foldl_of_mem {α : Type} (b : Nat) (l : List α) (F : Nat → α → Nat) (init : Nat) (x : α) (hx : x ∈ l)
    (h_base : ∀ init', b ≤ F init' x) (h_exp : ∀ a z, a ≤ F a z) : b ≤ l.foldl F init := by
  induction l generalizing init with
  | nil => exact absurd hx (by simp)
  | cons head tail ih =>
    simp [List.foldl]
    have h_cases : x = head ∨ x ∈ tail := by simpa using hx
    rcases h_cases with (h_eq | hx')
    · have h_b_le_F : b ≤ F init x := h_base init
      have h_b_le_F' : b ≤ F init head := h_eq ▸ h_b_le_F
      have h_F_foldl : F init head ≤ tail.foldl F (F init head) :=
        foldl_ge_init (h_nondec := h_exp) (xs := tail) (init := F init head)
      exact le_trans h_b_le_F' h_F_foldl
    · exact ih (F init head) hx'

/-- If the step function is non-increasing in the accumulator
(i.e., `f a i ≤ a` for all `a` and `i`), then `foldl f init xs ≤ init`.
This holds for any `Preorder α`, generalizing the `Nat`-only case. -/
lemma foldl_le_init {α : Type u} {β : Type v} [Preorder α] (f : α → β → α)
    (h_noninc : ∀ (a : α) (i : β), f a i ≤ a) (l : List β) (a : α) :
    (l.foldl f a) ≤ a := by
  induction' l with i l ih generalizing a
  · exact le_refl a
  · have h_fa : f a i ≤ a := h_noninc a i
    have h_fold : (l.foldl f (f a i)) ≤ f a i := ih (f a i)
    simpa [List.foldl] using le_trans h_fold h_fa

/-- If the step function is monotone in the accumulator, then `foldl` is also monotone:
`a₁ ≤ a₂` implies `foldl step a₁ xs ≤ foldl step a₂ xs`. -/
lemma foldl_mono {α : Type} {step : Nat → α → Nat} {a₁ a₂ : Nat} {xs : List α}
    (hmono : ∀ (a₁ a₂ : Nat) (x : α), a₁ ≤ a₂ → step a₁ x ≤ step a₂ x)
    (hle : a₁ ≤ a₂) : List.foldl step a₁ xs ≤ List.foldl step a₂ xs := by
  induction' xs with x xs ih generalizing a₁ a₂
  · exact hle
  · simp
    exact ih (hmono a₁ a₂ x hle)

/-- For a non-decreasing monotone step, any element `x` in the list satisfies
`step init x ≤ foldl step init xs`. -/
lemma foldl_ge_mem_step {α : Type} {step : Nat → α → Nat} {init : Nat} {xs : List α} {x : α}
    (h_nondec : ∀ (acc : Nat) (x : α), acc ≤ step acc x)
    (h_mono : ∀ (a₁ a₂ : Nat) (x : α), a₁ ≤ a₂ → step a₁ x ≤ step a₂ x)
    (h_mem : x ∈ xs) :
    step init x ≤ List.foldl step init xs := by
  induction xs generalizing init with
  | nil => exact absurd h_mem (by simp)
  | cons z zs ih =>
    rw [List.mem_cons] at h_mem
    rcases h_mem with (h_eq | h_mem')
    · rw [h_eq]
      simp
      exact foldl_ge_init h_nondec (init := step init z)
    · simp
      have h_init_le : init ≤ step init z := h_nondec init z
      have h_step : step init x ≤ step (step init z) x := h_mono init (step init z) x h_init_le
      have h_ih : step (step init z) x ≤ List.foldl step (step init z) zs :=
        ih h_mem' (init := step init z)
      exact Nat.le_trans h_step h_ih

/-- For a non-increasing monotone step, any element `x` in the list satisfies
`foldl step init xs ≤ step init x`. -/
lemma foldl_le_mem_step {α : Type} {step : Nat → α → Nat} {init : Nat} {xs : List α} {x : α}
    (h_noninc : ∀ (acc : Nat) (x : α), step acc x ≤ acc)
    (h_mono : ∀ (a₁ a₂ : Nat) (x : α), a₁ ≤ a₂ → step a₁ x ≤ step a₂ x)
    (h_mem : x ∈ xs) :
    List.foldl step init xs ≤ step init x := by
  induction xs generalizing init with
  | nil => exact absurd h_mem (by simp)
  | cons z zs ih =>
    rw [List.mem_cons] at h_mem
    rcases h_mem with (h_eq | h_mem')
    · rw [h_eq]
      simp
      exact foldl_le_init step h_noninc zs (step init z)
    · simp
      have h_step : step (step init z) x ≤ step init x :=
        h_mono (step init z) init x (h_noninc init z)
      have h_ih : List.foldl step (step init z) zs ≤ step (step init z) x :=
        ih h_mem' (init := step init z)
      exact Nat.le_trans h_ih h_step

/-- If two folding functions `f` and `g` are pointwise equal (i.e., `∀ b a, f b a = g b a`),
then `foldl f init l = foldl g init l`. This is a congruence lemma for `foldl` that allows
replacing the step function with an equal one without changing the fold result. -/
lemma foldl_congr {α β : Type} (f g : β → α → β) (l : List α) (init : β) (h : ∀ b a, f b a = g b a) :
    List.foldl f init l = List.foldl g init l := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp [ih, h]

/-- If two folding functions `f` and `g` agree on all elements of the list `l`
(i.e., `∀ a ∈ l, ∀ b, f b a = g b a`), then `foldl f init l = foldl g init l`.
This is a weaker variant of `foldl_congr` that only requires equality on the elements
actually present in the list, rather than on all possible values. -/
lemma foldl_congr_of_mem {α β : Type} (l : List α) (f g : β → α → β) (init : β)
    (h : ∀ a ∈ l, ∀ b, f b a = g b a) : List.foldl f init l = List.foldl g init l := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, List.foldl_cons]
    rw [h a (by simp) init]
    apply ih
    intro a' ha'
    exact h a' (by simp [ha'])

/-- If each step of `f` ignores its second argument and returns the accumulator unchanged
    (i.e. `f a b = a`), then folding `f` over a list leaves the initial accumulator unchanged. -/
lemma foldl_eq_self {α β : Type} (f : α → β → α) (hf : ∀ a b, f a b = a) (init : α) (l : List β) :
    List.foldl f init l = init := by
  induction' l with head tail ih generalizing init
  · rfl
  · rw [List.foldl, hf init head, ih]

/-- If each step of `f` returns the accumulator unchanged for every element `a` in the list `l`
    (i.e., `∀ a ∈ l, ∀ b', f b' a = b'`), then folding `f` over `l` leaves the initial accumulator
    unchanged. This is a per-element weakening of `foldl_eq_self`, where the identity condition
    only needs to hold for the elements actually present in the list. -/
lemma foldl_eq_initial_of_const {α β : Type} (f : β → α → β) (l : List α) (b : β)
    (h : ∀ a ∈ l, ∀ b' : β, f b' a = b') : List.foldl f b l = b := by
  induction' l with a as ih generalizing b
  · rfl
  · have ha : ∀ b', f b' a = b' := h a (by simp)
    rw [List.foldl_cons, ha b]
    apply ih
    intro a' ha'
    exact h a' (by simp [ha'])

/-- If `f` always returns `0`, then folding addition of `f` over a list
    leaves the initial accumulator unchanged. -/
lemma foldl_add_zero {α β : Type} [AddMonoid α] (f : β → α) (hf : ∀ x, f x = 0) (init : α) (l : List β) :
    List.foldl (fun acc x => acc + f x) init l = init := by
  refine foldl_eq_self (fun acc x => acc + f x) ?_ init l
  intro a b
  simp [hf b]

/-! ### Bounded measure via foldl

These lemmas use a measure function `m : α → Nat` to establish that
if the step function produces values whose measure is bounded by the measures
of its input arguments, then the measure of the fold result is correspondingly bounded. -/

/-- If for all `a`, `b`, `f a b` has `m`-measure ≤ both `m a` and `m b`,
then `foldl f init xs` has `m`-measure ≤ `m init` and ≤ every element in `xs`.
This is useful when `m` measures some cost/size and `f` never increases it. -/
lemma foldl_selective_measure_le {α : Type u} (m : α → Nat) (f : α → α → α)
    (h_bound_init : ∀ a b, m (f a b) ≤ m a)
    (h_bound_arg : ∀ a b, m (f a b) ≤ m b)
    (xs : List α) (init : α) :
    m (List.foldl f init xs) ≤ m init ∧ (∀ y ∈ xs, m (List.foldl f init xs) ≤ m y) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_ih := ih (f init x)
    rcases h_ih with ⟨hle_new, hall⟩
    have h_new_le_init : m (f init x) ≤ m init := h_bound_init init x
    have h_new_le_x : m (f init x) ≤ m x := h_bound_arg init x
    refine ⟨le_trans hle_new h_new_le_init, ?_⟩
    intro y hy
    cases hy with
    | head _ => exact le_trans hle_new h_new_le_x
    | tail _ hy' => exact hall y hy'

/-! ### Foldl with associative operation and identity element -/

/-- For an associative binary operation `f` with identity element `id` (both left and right),
folding `f` over `l` starting from accumulator `a` equals `f a` applied to the fold from `id`.
This generalizes properties of monoids: for example,
`foldl (+) a l = a + foldl (+) 0 l` follows by taking `h_assoc := add_assoc`,
`h_id_left a := zero_add a`, `h_id_right a := add_zero a`. -/
lemma foldl_eq_of_assoc_identity {α : Type _} (f : α → α → α) (id : α)
    (h_assoc : ∀ a b c, f a (f b c) = f (f a b) c)
    (h_id_left : ∀ a, f id a = a)
    (h_id_right : ∀ a, f a id = a)
    (l : List α) (a : α) :
    (l.foldl f a) = f a (l.foldl f id) := by
  induction' l with x xs ih generalizing a
  · rw [List.foldl_nil, List.foldl_nil, h_id_right a]
  · rw [List.foldl_cons, List.foldl_cons]
    rw [h_id_left x]
    rw [ih (f a x), ih x]
    rw [h_assoc]

/-- In an `AddMonoid`, left-folding addition from `b` equals `b` plus folding from `0`.
This is a convenient special case of `foldl_eq_of_assoc_identity` for `(+)`. -/
lemma foldl_add_eq_add_foldl_zero {α : Type _} [AddMonoid α] (l : List α) (b : α) :
    l.foldl (· + ·) b = b + l.foldl (· + ·) 0 := by
  simpa using
    foldl_eq_of_assoc_identity (· + ·) 0 (fun a b c => (add_assoc a b c).symm) zero_add add_zero l b

/-! ### Foldl with `maxStep` and `minStep` -/

/-- Folding `maxStep f` over a list bounds `f x` from above for any `x ∈ xs`:
`f x ≤ foldl (maxStep f) init xs`. -/
lemma foldl_maxStep_ge_mem {α : Type} {f : α → Nat} {init : Nat} {xs : List α} {x : α}
    (h_mem : x ∈ xs) :
    f x ≤ List.foldl (maxStep f) init xs := by
  have h_nondec : ∀ (acc : Nat) (x : α), acc ≤ maxStep f acc x := by
    intro acc x; exact maxStep_ge_acc
  have h_mono : ∀ (a₁ a₂ : Nat) (x : α), a₁ ≤ a₂ → maxStep f a₁ x ≤ maxStep f a₂ x := by
    intro a₁ a₂ x h; exact maxStep_mono h
  have h_step : f x ≤ maxStep f init x := maxStep_ge_val
  have h_fold : maxStep f init x ≤ List.foldl (maxStep f) init xs :=
    foldl_ge_mem_step h_nondec h_mono h_mem
  exact Nat.le_trans h_step h_fold

/-- Folding `minStep f` over a list bounds `f x` from below for any `x ∈ xs`:
`foldl (minStep f) init xs ≤ f x`. -/
lemma foldl_minStep_le_mem {α : Type} {f : α → Nat} {init : Nat} {xs : List α} {x : α}
    (h_mem : x ∈ xs) :
    List.foldl (minStep f) init xs ≤ f x := by
  have h_noninc : ∀ (acc : Nat) (x : α), minStep f acc x ≤ acc := by
    intro acc x; exact minStep_le_acc
  have h_mono : ∀ (a₁ a₂ : Nat) (x : α), a₁ ≤ a₂ → minStep f a₁ x ≤ minStep f a₂ x := by
    intro a₁ a₂ x h; exact minStep_mono h
  have h_step : minStep f init x ≤ f x := minStep_le_val
  have h_fold : List.foldl (minStep f) init xs ≤ minStep f init x :=
    foldl_le_mem_step h_noninc h_mono h_mem
  exact Nat.le_trans h_fold h_step

/-! ### `maxOverList` — fold with optional valuation -/

/-- Fold over `cands` with a valuation `f : α → Option β`.
For each `x` where `f x = some v`, update `best` to `max best v`.
Returns the overall maximum of `best` and all covered valuations. -/
def maxOverList {α β : Type} [LinearOrder β] (cands : List α) (f : α → Option β) (best : β) : β :=
  match cands with
  | [] => best
  | x :: xs =>
    match f x with
    | none => maxOverList xs f best
    | some v => maxOverList xs f (max best v)

/-- `maxOverList` never decreases the initial `best`. -/
lemma maxOverList_ge_best {α β : Type} [LinearOrder β]
    (cands : List α) (f : α → Option β) (best : β) :
    best ≤ maxOverList cands f best := by
  revert best
  induction cands with
  | nil => intro best; exact le_refl best
  | cons y ys ih =>
    intro best
    unfold maxOverList
    cases f y with
    | none => apply ih
    | some v =>
      apply le_trans (le_max_left _ _)
      apply ih

/-- If `x` is a candidate with valuation `some v`, then `v` does not exceed the
overall maximum. -/
lemma maxOverList_covers {α β : Type} [LinearOrder β]
    (cands : List α) (f : α → Option β) (best : β)
    (x : α) (hx : x ∈ cands) (v : β) (hval : f x = some v) :
    v ≤ maxOverList cands f best := by
  revert best hx hval
  induction cands with
  | nil =>
    intro best hx hval; simp at hx
  | cons y ys ih =>
    intro best hx hval
    simp at hx
    rcases hx with (rfl | hxys)
    · -- x = y, the head element
      unfold maxOverList
      rw [hval]
      apply le_trans (le_max_right _ _)
      apply maxOverList_ge_best
    · -- x is in the tail
      unfold maxOverList
      cases h : f y with
      | none => apply ih best hxys hval
      | some v' => apply ih (max best v') hxys hval

/-- The result of `maxOverList` is either the initial `best` or some valuation
`v` produced by `f`. -/
lemma maxOverList_attained {α β : Type} [LinearOrder β]
    (cands : List α) (f : α → Option β) (best : β) :
    maxOverList cands f best = best ∨
    ∃ (x : α) (v : β), f x = some v ∧ maxOverList cands f best = v := by
  revert best
  induction cands with
  | nil =>
    intro best; left; rfl
  | cons y ys ih =>
    intro best
    unfold maxOverList
    cases h : f y with
    | none =>
      apply ih best
    | some v =>
      dsimp
      rcases ih (max best v) with (hgo | hgo)
      · -- recursive result equals max best v
        rw [hgo]
        by_cases hle : v ≤ best
        · left; exact max_eq_left hle
        · have hge : best ≤ v := le_of_lt (lt_of_not_ge hle)
          right; exact ⟨y, v, h, max_eq_right hge⟩
      · -- recursive result equals some valuation
        rcases hgo with ⟨x, v', hxval, hxeq⟩
        right; exact ⟨x, v', hxval, hxeq⟩

/-! ### Double-folding over all ordered pairs -/

/-- The inner fold of the double-folding max structure:
for a fixed `d₁`, fold `maxStep (f d₁)` over `xs` to get the maximum `f d₁ d₂`
over all `d₂ ∈ xs`. -/
def outerMaxStep (f : Nat → Nat → Nat) (xs : List Nat) (acc d₁ : Nat) : Nat :=
  List.foldl (maxStep (f d₁)) acc xs

/-- The inner fold of the double-folding min structure:
for a fixed `d₁`, fold `minStep (f d₁)` over `xs` to get the minimum `f d₁ d₂`
over all `d₂ ∈ xs`. -/
def outerMinStep (f : Nat → Nat → Nat) (xs : List Nat) (acc d₁ : Nat) : Nat :=
  List.foldl (minStep (f d₁)) acc xs

/-- Maximum of `f d₁ d₂` over all ordered pairs `(d₁, d₂) ∈ xs × xs`.
This is the user-facing API built from `outerMaxStep`. -/
def doubleMaxOver (f : Nat → Nat → Nat) (xs : List Nat) : Nat :=
  List.foldl (outerMaxStep f xs) 0 xs

/-- `outerMaxStep` is non-decreasing in the accumulator. -/
lemma outerMaxStep_ge_acc {f : Nat → Nat → Nat} {xs : List Nat} {acc d₁ : Nat} :
    acc ≤ outerMaxStep f xs acc d₁ :=
  foldl_ge_init (λ _ _ => maxStep_ge_acc (f := f d₁))

/-- `outerMaxStep` is monotone in the accumulator. -/
lemma outerMaxStep_mono {f : Nat → Nat → Nat} {xs : List Nat} {a₁ a₂ d₁ : Nat} (h : a₁ ≤ a₂) :
    outerMaxStep f xs a₁ d₁ ≤ outerMaxStep f xs a₂ d₁ :=
  foldl_mono (λ _ _ _ hle => maxStep_mono hle) h

/-- `outerMaxStep` bounds `f d₁ d₂` from above when `d₂ ∈ xs`. -/
lemma outerMaxStep_ge_val {f : Nat → Nat → Nat} {xs : List Nat} {d₁ d₂ acc : Nat}
    (hd₂ : d₂ ∈ xs) : f d₁ d₂ ≤ outerMaxStep f xs acc d₁ :=
  foldl_maxStep_ge_mem hd₂

/-- `outerMinStep` is non-increasing in the accumulator. -/
lemma outerMinStep_le_acc {f : Nat → Nat → Nat} {xs : List Nat} {acc d₁ : Nat} :
    outerMinStep f xs acc d₁ ≤ acc :=
  foldl_le_init (minStep (f d₁)) (λ _ _ => minStep_le_acc (f := f d₁)) xs acc

/-- `outerMinStep` is monotone in the accumulator. -/
lemma outerMinStep_mono {f : Nat → Nat → Nat} {xs : List Nat} {a₁ a₂ d₁ : Nat} (h : a₁ ≤ a₂) :
    outerMinStep f xs a₁ d₁ ≤ outerMinStep f xs a₂ d₁ :=
  foldl_mono (λ _ _ _ hle => minStep_mono hle) h

/-- `outerMinStep` bounds `f d₁ d₂` from below when `d₂ ∈ xs`. -/
lemma outerMinStep_le_val {f : Nat → Nat → Nat} {xs : List Nat} {d₁ d₂ acc : Nat}
    (hd₂ : d₂ ∈ xs) : outerMinStep f xs acc d₁ ≤ f d₁ d₂ :=
  foldl_minStep_le_mem hd₂

/-- Double-fold max bounds all `f d₁ d₂` from above when `d₁, d₂ ∈ xs`:
`f d₁ d₂ ≤ foldl (outerMaxStep f xs) 0 xs`. -/
lemma double_fold_max_ge {f : Nat → Nat → Nat} {xs : List Nat} {d₁ d₂ : Nat}
    (hd₁ : d₁ ∈ xs) (hd₂ : d₂ ∈ xs) :
    f d₁ d₂ ≤ List.foldl (outerMaxStep f xs) 0 xs := by
  have h_val : f d₁ d₂ ≤ outerMaxStep f xs 0 d₁ := outerMaxStep_ge_val hd₂
  have h_step_nondec : ∀ (acc : Nat) (x : Nat), acc ≤ outerMaxStep f xs acc x :=
    λ acc x => outerMaxStep_ge_acc
  have h_step_mono : ∀ (a₁ a₂ : Nat) (x : Nat), a₁ ≤ a₂ →
      outerMaxStep f xs a₁ x ≤ outerMaxStep f xs a₂ x :=
    λ a₁ a₂ x h => outerMaxStep_mono h
  have h_outer : outerMaxStep f xs 0 d₁ ≤ List.foldl (outerMaxStep f xs) 0 xs :=
    foldl_ge_mem_step h_step_nondec h_step_mono hd₁
  exact Nat.le_trans h_val h_outer

/-- Double-fold min bounds all `f d₁ d₂` from below when `d₁, d₂ ∈ xs`:
`foldl (outerMinStep f xs) init xs ≤ f d₁ d₂`. -/
lemma double_fold_min_le {f : Nat → Nat → Nat} {xs : List Nat} {d₁ d₂ init : Nat}
    (hd₁ : d₁ ∈ xs) (hd₂ : d₂ ∈ xs) :
    List.foldl (outerMinStep f xs) init xs ≤ f d₁ d₂ := by
  have h_step_noninc : ∀ (acc : Nat) (x : Nat), outerMinStep f xs acc x ≤ acc :=
    λ acc x => outerMinStep_le_acc
  have h_step_mono : ∀ (a₁ a₂ : Nat) (x : Nat), a₁ ≤ a₂ →
      outerMinStep f xs a₁ x ≤ outerMinStep f xs a₂ x :=
    λ a₁ a₂ x h => outerMinStep_mono h
  have h_outer : List.foldl (outerMinStep f xs) init xs ≤ outerMinStep f xs init d₁ :=
    foldl_le_mem_step h_step_noninc h_step_mono hd₁
  have h_val : outerMinStep f xs init d₁ ≤ f d₁ d₂ := outerMinStep_le_val hd₂
  exact Nat.le_trans h_outer h_val

/-! ### Folding `min` over a `LinearOrder α` list

These lemmas generalize the `Nat`-only `foldl_min_le_init` / `foldl_min_le_of_mem`
from `general.List` to any `LinearOrder α`, using `min` as the step function. -/

/-- Folding `min` starting from `a` gives a result `≤ a`.
For any `LinearOrder α`, `xs.foldl (fun acc y => min y acc) a ≤ a`.
This is the `LinearOrder` generalization of `List.foldl_min_le_init` (which is `Nat`-only). -/
lemma foldl_min_init_le {α : Type} [LinearOrder α] (a : α) (xs : List α) :
    xs.foldl (fun acc y => min y acc) a ≤ a := by
  induction xs generalizing a with
  | nil => rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    have h1 : ys.foldl (fun acc y => min y acc) (min y a) ≤ min y a := ih (min y a)
    have h2 : min y a ≤ a := min_le_right _ _
    exact le_trans h1 h2

/-- If `x ∈ xs`, then folding `min` starting from `a` gives a result `≤ x`.
For any `LinearOrder α`, `xs.foldl (fun acc y => min y acc) a ≤ x` when `x ∈ xs`.
This is the `LinearOrder` generalization of `List.foldl_min_le_of_mem` (which is `Nat`-only). -/
lemma foldl_min_flip_le_of_mem {α : Type} [LinearOrder α] (a : α) (xs : List α) {x : α} (hx : x ∈ xs) :
    xs.foldl (fun acc y => min y acc) a ≤ x := by
  induction hx generalizing a with
  | head ys =>
    rw [List.foldl_cons]
    have h1 : ys.foldl (fun acc y => min y acc) (min x a) ≤ min x a :=
      foldl_min_init_le (min x a) ys
    have h2 : min x a ≤ x := min_le_left _ _
    exact le_trans h1 h2
  | tail b _ ih =>
    rw [List.foldl_cons]
    exact ih (min b a)

/-- Folding `min` (standard argument order) starting from `a` gives a result `≤ a`.
For any `LinearOrder α`, `xs.foldl min a ≤ a`.
This is the standard-order counterpart of `foldl_min_init_le` which uses flipped arguments. -/
lemma foldl_min_le_initial {α : Type} [LinearOrder α] (a : α) (xs : List α) :
    xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact le_refl a
  | cons y ys ih =>
    rw [List.foldl_cons]
    calc
      ys.foldl min (min a y) ≤ min a y := ih (min a y)
      _ ≤ a := min_le_left _ _

/-- If `x ∈ xs`, then folding `min` (standard argument order) starting from `a` gives a result `≤ x`.
For any `LinearOrder α`, `xs.foldl min a ≤ x` when `x ∈ xs`.
This is the standard-order counterpart of `foldl_min_flip_le_of_mem` which uses flipped arguments. -/
lemma foldl_min_le_mem {α : Type} [LinearOrder α] (a : α) (xs : List α) {x : α} (hx : x ∈ xs) :
    xs.foldl min a ≤ x := by
  induction hx generalizing a with
  | head ys =>
    rw [List.foldl_cons]
    have h1 : ys.foldl min (min a x) ≤ min a x :=
      foldl_min_le_initial (min a x) ys
    have h2 : min a x ≤ x := min_le_right _ _
    exact le_trans h1 h2
  | tail b _ ih =>
    rw [List.foldl_cons]
    exact ih (min a b)

/-! ### `minFold` — fold minimum over a list with projection -/

/-- Fold the minimum of `f x` over `xs`, starting from an initial bound `init`.
`minFold f init xs = min init (min_{x ∈ xs} f x)`.
This is a convenience wrapper around `foldl (minStep f) init xs`. -/
def minFold {α : Type} (f : α → Nat) (init : Nat) (xs : List α) : Nat :=
  xs.foldl (minStep f) init

/-- `minFold` never exceeds the initial bound. -/
lemma minFold_le_init {α : Type} {f : α → Nat} {init : Nat} {xs : List α} :
    minFold f init xs ≤ init :=
  foldl_le_init (minStep f) (λ _ _ => minStep_le_acc) xs init

/-- For any `x ∈ xs`, `minFold f init xs ≤ f x`. -/
lemma minFold_le_mem {α : Type} {f : α → Nat} {init : Nat} {xs : List α} {x : α}
    (h_mem : x ∈ xs) : minFold f init xs ≤ f x := by
  unfold minFold
  exact foldl_minStep_le_mem h_mem

/-! ### `minOn` — fold `Nat.min` over a list with projection using `foldr` -/

/-- Fold `Nat.min` over a list using a projection `f` and a `default` starting value.
`minOn default f as` computes `min(default, min_{a ∈ as} f a)` via `foldr`.
Contrast with `minFold`, which uses `foldl` with `minStep`. -/
def minOn (default : Nat) (f : α → Nat) (as : List α) : Nat :=
  as.foldr (fun a acc => Nat.min (f a) acc) default


theorem minOn_nil (default : Nat) (f : α → Nat) : minOn default f [] = default := rfl


theorem minOn_cons (default : Nat) (f : α → Nat) (a : α) (as : List α) :
    minOn default f (a :: as) = Nat.min (f a) (minOn default f as) := rfl

/-! ### `List.all` with `decide` for minimum le -/

/-- If every element `x` in a nonempty list `l` satisfies `l.minimum_of_length_pos hpos ≤ x`,
then `l.all (fun x => decide (l.minimum_of_length_pos hpos ≤ x)) = true`.
This bridges the `Prop`-level lemma `List.minimum_of_length_pos_le_of_mem` to the `Bool`-level `List.all` combinator. -/
lemma all_minimum_of_length_pos_le {α : Type} [LinearOrder α] (l : List α) (hpos : 0 < l.length) :
    l.all (fun x => decide (l.minimum_of_length_pos hpos ≤ x)) = true := by
  rw [List.all_eq_true]
  intro x hx
  have hle := List.minimum_of_length_pos_le_of_mem hx hpos
  exact decide_eq_true hle

/-! ### `maxOfFilter` — maximum value of `f x` over those `x` in `xs` where `p x` holds -/

/-- Step function for `maxOfFilter`: conditionally takes the max of the accumulator
and `f x` when `p x` holds, otherwise leaves the accumulator unchanged. -/
def maxOfFilterStep {α : Type} (f : α → Nat) (p : α → Bool) (m : Nat) (x : α) : Nat :=
  if p x then Nat.max m (f x) else m

/-- Maximum value of `f x` over those `x` in `xs` where `p x` holds.
Returns `0` when no element satisfies `p`. -/
def maxOfFilter {α : Type} (f : α → Nat) (p : α → Bool) (xs : List α) : Nat :=
  xs.foldl (maxOfFilterStep f p) 0


theorem maxOfFilter_nil {α : Type} (f : α → Nat) (p : α → Bool) :
    maxOfFilter f p [] = 0 := rfl

/-- For a max-like fold with `maxOfFilterStep`, starting from an initial value `a` is equivalent to
taking the max of `a` with the result starting from `0`. -/
theorem foldl_maxOfFilterStep_eq_max_left {α : Type} (f : α → Nat) (p : α → Bool) (xs : List α)
    (a : Nat) :
    List.foldl (maxOfFilterStep f p) a xs =
    Nat.max a (List.foldl (maxOfFilterStep f p) 0 xs) := by
  induction xs generalizing a with
  | nil => simp [maxOfFilterStep]
  | cons x xs ih =>
      by_cases h : p x = true
      · have ga : maxOfFilterStep f p a x = Nat.max a (f x) := by
          dsimp [maxOfFilterStep]; simp [h]
        have g0 : maxOfFilterStep f p 0 x = f x := by
          dsimp [maxOfFilterStep]; simp [h]
        rw [List.foldl_cons, ga, List.foldl_cons, g0]
        rw [ih (a := Nat.max a (f x)), ih (a := f x)]
        exact Nat.max_assoc a (f x) (List.foldl (maxOfFilterStep f p) 0 xs)
      · have ga : maxOfFilterStep f p a x = a := by
          dsimp [maxOfFilterStep]; simp [h]
        have g0 : maxOfFilterStep f p 0 x = 0 := by
          dsimp [maxOfFilterStep]; simp [h]
        rw [List.foldl_cons, ga, List.foldl_cons, g0]
        exact ih a

/-- When `p x = true` and `x` is the head of a cons, `maxOfFilter f p (x :: xs)` simplifies to
`Nat.max (f x) (maxOfFilter f p xs)`. -/
theorem maxOfFilter_cons_true {α : Type} (f : α → Nat) (p : α → Bool) (x : α) (xs : List α)
    (hp : p x = true) : maxOfFilter f p (x :: xs) = Nat.max (f x) (maxOfFilter f p xs) := by
  calc
    maxOfFilter f p (x :: xs)
        = List.foldl (maxOfFilterStep f p) 0 (x :: xs) := rfl
    _ = List.foldl (maxOfFilterStep f p) (maxOfFilterStep f p 0 x) xs := by rw [List.foldl_cons]
    _ = List.foldl (maxOfFilterStep f p) (Nat.max 0 (f x)) xs := by simp [maxOfFilterStep, hp]
    _ = List.foldl (maxOfFilterStep f p) (f x) xs := by simp
    _ = Nat.max (f x) (List.foldl (maxOfFilterStep f p) 0 xs) := by
          simpa using foldl_maxOfFilterStep_eq_max_left f p xs (a := f x)
    _ = Nat.max (f x) (maxOfFilter f p xs) := rfl

/-! ### `maxOfFilteredPairs` — maximum over filtered pairs -/

/-- Fold over a list of pairs: for each `(a, b)` where `pred a` holds, accumulate `max acc b`;
    otherwise keep `acc`. Returns the maximum of `acc` and all `b` whose paired `a` satisfies `pred`. -/
def maxOfFilteredPairs {α β : Type} [LinearOrder β] (pairs : List (α × β)) (pred : α → Bool) (acc : β) : β :=
  pairs.foldl (fun acc' (a, b) => if pred a then max acc' b else acc') acc


lemma maxOfFilteredPairs_nil {α β : Type} [LinearOrder β] (pred : α → Bool) (acc : β) :
    maxOfFilteredPairs [] pred acc = acc := rfl


lemma maxOfFilteredPairs_cons {α β : Type} [LinearOrder β] (a : α) (b : β) (pairs : List (α × β)) (pred : α → Bool) (acc : β) :
    maxOfFilteredPairs ((a, b) :: pairs) pred acc =
    maxOfFilteredPairs pairs pred (if pred a then max acc b else acc) := rfl

/-- The result of `maxOfFilteredPairs` is at least the initial accumulator. -/
lemma maxOfFilteredPairs_ge_acc {α β : Type} [LinearOrder β] (pairs : List (α × β)) (pred : α → Bool) :
    ∀ (acc : β), acc ≤ maxOfFilteredPairs pairs pred acc := by
  induction pairs with
  | nil => intro acc; exact le_refl acc
  | cons p ps ih =>
    intro acc
    rcases p with ⟨a, b⟩
    simp [maxOfFilteredPairs]
    split_ifs with h
    · have hmax : acc ≤ max acc b := le_max_left _ _
      exact le_trans hmax (ih (max acc b))
    · exact ih acc

/-- `maxOfFilteredPairs` is monotone in the initial accumulator. -/
lemma maxOfFilteredPairs_mono {α β : Type} [LinearOrder β] (pairs : List (α × β)) (pred : α → Bool) :
    ∀ (acc₁ acc₂ : β), acc₁ ≤ acc₂ → maxOfFilteredPairs pairs pred acc₁ ≤ maxOfFilteredPairs pairs pred acc₂ := by
  induction pairs with
  | nil => intro acc₁ acc₂ h; exact h
  | cons p ps ih =>
    intro acc₁ acc₂ h
    rcases p with ⟨a, b⟩
    simp [maxOfFilteredPairs]
    split_ifs with hp
    · apply ih
      exact max_le_max h (le_refl b)
    · exact ih acc₁ acc₂ h

/-! ### `foldRev` — left fold over a list, reversing the final result -/

/-- `foldRev f xs init` folds the list `xs` from left to right using step function
`f : α → List α → List α`, starting with accumulator `init`, and reverses the final result.
This is useful for stack-based algorithms where processing order matches list order but
the final result needs to be in the original direction.
Equivalent to `(xs.foldl (fun acc a => f a acc) init).reverse`. -/
def foldRev (f : α → List α → List α) (xs : List α) (init : List α) : List α :=
  match xs with
  | [] => init.reverse
  | a :: rest => foldRev f rest (f a init)

/-- Induction principle for `foldRev`: if a boolean property `prop` holds for
`init.reverse`, and for any `a` and `stack` where `prop stack.reverse` holds,
`prop (f a stack).reverse` also holds, then `prop` holds for `foldRev f xs init`. -/
lemma foldRev_preserves_prop {α : Type} (f : α → List α → List α) (prop : List α → Bool)
    (xs init : List α) (h_init : prop init.reverse = true)
    (h_step : ∀ a stack, prop stack.reverse = true → prop (f a stack).reverse = true) :
    prop (foldRev f xs init) = true := by
  induction' xs with a rest ih generalizing init
  · simpa [foldRev] using h_init
  · have h_new : prop (f a init).reverse = true := h_step a init h_init
    simpa [foldRev] using ih (f a init) h_new

/-! ### Relation between `foldl` and `foldr` for commutative-associative operations -/

/-- For an `AddCommMonoid α`, `foldl (+) h t = h + foldr (+) 0 t`.
This shows that left-folding `(+)` and right-folding `(+)` differ only by the initial
accumulator, reflecting that addition is commutative and associative. -/
lemma foldl_add_eq_add_foldr_add {α : Type u} [AddCommMonoid α] (h : α) (t : List α) :
    t.foldl (· + ·) h = h + t.foldr (· + ·) 0 := by
  induction t generalizing h with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl, List.foldr]
    rw [ih (h + x)]
    simp [add_comm, add_left_comm, add_assoc]

/-- `foldl (+) 0 l = l.sum` for any `AddCommMonoid α`.
This is a direct corollary of `foldl_add_eq_add_foldr_add` and the definition of `List.sum`. -/
lemma foldl_add_eq_sum {α : Type u} [AddCommMonoid α] (l : List α) :
    l.foldl (· + ·) 0 = l.sum := by
  rw [foldl_add_eq_add_foldr_add 0 l, zero_add, List.sum]

/-! ### Distributing the initial accumulator through foldl with addition -/

/-- For any `f : α → β` into an `AddCommMonoid β`, folding `(acc + f x)` over a list distributes
over the initial accumulator: `foldl (λ acc x => acc + f x) n xs = n + foldl (λ acc x => acc + f x) 0 xs`.
This is useful when the step function adds a projection of the element to the accumulator. -/
lemma foldl_add_self {α β : Type} [AddCommMonoid β] (f : α → β) (n : β) (xs : List α) :
    List.foldl (fun acc x => acc + f x) n xs = n + List.foldl (fun acc x => acc + f x) 0 xs := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    rw [ih (n + f x), ih (f x)]
    abel

/-- Folding addition of a projected `Nat` value over a list is equal to the sum of the mapped
list: `foldl (λ acc x => acc + f x) 0 xs = (xs.map f).sum`. -/
lemma foldl_add_eq_sum_map {α : Type} (f : α → Nat) (xs : List α) :
    List.foldl (fun acc x => acc + f x) 0 xs = (xs.map f).sum := by
  calc
    List.foldl (fun acc x => acc + f x) 0 xs = (xs.map f).foldl (· + ·) 0 := by
      simpa [List.foldl_map]
    _ = (xs.map f).sum := foldl_add_eq_sum _

/-- Sum the results of applying a function to each element of a list.
This is a convenience combinator; `sumMap f l = (l.map f).sum`. -/
def sumMap {α : Type} (f : α → Nat) (l : List α) : Nat :=
  l.foldl (fun acc a => acc + f a) 0


lemma sumMap_eq_map_sum {α : Type} (f : α → Nat) (l : List α) :
    sumMap f l = (l.map f).sum :=
  foldl_add_eq_sum_map f l

lemma sumMap_nil {α : Type} (f : α → Nat) : sumMap f [] = 0 := rfl

lemma sumMap_cons {α : Type} (f : α → Nat) (a : α) (l : List α) :
    sumMap f (a :: l) = f a + sumMap f l := by
  unfold sumMap
  simp [List.foldl, foldl_add_self f (f a) l]

lemma sumMap_append {α : Type} (f : α → Nat) (l₁ l₂ : List α) :
    sumMap f (l₁ ++ l₂) = sumMap f l₁ + sumMap f l₂ := by
  simp only [sumMap_eq_map_sum, List.map_append, List.sum_append]

/-! ### `avgMap` — projected integer average of a list of natural numbers -/

/-- Projected integer average (floor division) of a list via `f : α → Nat`.
Returns `0` for the empty list, otherwise `sumMap f xs / xs.length`.
This is the projected counterpart of `avg` (which works on `List Nat` directly). -/
def avgMap {α : Type} (f : α → Nat) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ => sumMap f xs / xs.length


lemma avgMap_nil {α : Type} (f : α → Nat) : avgMap f [] = 0 := rfl

lemma avgMap_cons {α : Type} (f : α → Nat) (x : α) (xs : List α) :
    avgMap f (x :: xs) = sumMap f (x :: xs) / (x :: xs).length := rfl

lemma avgMap_eq_div_of_ne_nil {α : Type} (f : α → Nat) {xs : List α} (h : xs ≠ []) :
    avgMap f xs = sumMap f xs / xs.length := by
  rcases List.exists_cons_of_ne_nil h with ⟨x, xs', rfl⟩
  rfl

/-! ### Finset intersection via foldl -/

/-- A value `w` is in the result of `foldl (· ∩ ·)` over Finsets iff it is in the starting
Finset and in `f a` for every `a ∈ ss`. This is the key lemma for reasoning about
intersecting Finsets derived from list elements (e.g., finding common words across strings). -/
lemma mem_foldl_inter_iff {α β : Type} [DecidableEq β] (w : β) (f : α → Finset β)
    (start : Finset β) (ss : List α) :
    w ∈ ss.foldl (fun acc a => acc ∩ f a) start ↔ w ∈ start ∧ ∀ a ∈ ss, w ∈ f a := by
  induction' ss with a as ih generalizing start
  · simp
  · rw [List.foldl, List.forall_mem_cons]
    rw [ih (start ∩ f a)]
    simp [Finset.mem_inter, and_assoc]

/-! ### `foldl` with `Nat.max` as the step function

These lemmas provide properties of `foldl` using `Nat.max` directly in the lambda
(as opposed to the `maxStep` wrapper). They are convenient for proving properties
of algorithms that compute the maximum of a projection `f : α → Nat` over a list. -/

/-- The accumulator is never greater than the result of folding `Nat.max`:
`acc ≤ l.foldl (fun acc' a => Nat.max acc' (f a)) acc`. -/
lemma foldl_max_ge_acc {α : Type} (f : α → Nat) (l : List α) (acc : Nat) :
    acc ≤ l.foldl (fun acc' a => Nat.max acc' (f a)) acc := by
  induction' l with hd tl ih generalizing acc
  · exact le_refl acc
  · rw [List.foldl_cons]
    have h := ih (Nat.max acc (f hd))
    exact le_trans (Nat.le_max_left _ _) h

/-- If `a ∈ l`, then `f a` is bounded above by the fold of `Nat.max`:
`f a ≤ l.foldl (fun acc b => Nat.max acc (f b)) init`. -/
lemma foldl_max_ge_of_mem {α : Type} (f : α → Nat) {l : List α} {a : α} (ha : a ∈ l) (init : Nat) :
    f a ≤ l.foldl (fun acc b => Nat.max acc (f b)) init := by
  induction' l with hd tl ih generalizing init a
  · exact absurd ha (List.not_mem_nil _)
  · rw [List.foldl_cons]
    cases ha with
    | head =>
        have h1 : f hd ≤ Nat.max init (f hd) := Nat.le_max_right _ _
        have h2 : Nat.max init (f hd) ≤
            tl.foldl (fun acc b => Nat.max acc (f b)) (Nat.max init (f hd)) :=
          foldl_max_ge_acc f tl (Nat.max init (f hd))
        exact le_trans h1 h2
    | tail _ ha' =>
        exact ih ha' (Nat.max init (f hd))

/-- If the fold of `Nat.max` with projection `f` over `l` starting from `0` equals `0`,
then `f a = 0` for every `a ∈ l`.
This is useful when the maximum value in a list is zero, implying all values are zero. -/
lemma foldl_max_eq_zero_imp_all_eq_zero {α : Type} (f : α → Nat) (l : List α)
    (hmax : l.foldl (fun m a => Nat.max m (f a)) 0 = 0) : ∀ a ∈ l, f a = 0 := by
  intro a ha
  have hle : f a ≤ l.foldl (fun m x => Nat.max m (f x)) 0 :=
    foldl_max_ge_of_mem f ha 0
  rw [hmax] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Folding `Nat.max` with an accumulator `acc` is equivalent to taking the max of `acc`
with the fold starting from `0`:
`l.foldl (fun acc' a' => Nat.max acc' (f a')) acc = Nat.max acc (l.foldl ... 0)`. -/
lemma foldl_max_eq_max_acc_foldl_zero {α : Type} (f : α → Nat) (l : List α) (acc : Nat) :
    l.foldl (fun acc' a' => Nat.max acc' (f a')) acc =
    Nat.max acc (l.foldl (fun acc' a' => Nat.max acc' (f a')) 0) := by
  induction' l with hd tl ih generalizing acc
  · simp
  · rw [List.foldl_cons, List.foldl_cons]
    rw [ih (Nat.max acc (f hd))]
    have hzero : Nat.max 0 (f hd) = f hd := Nat.zero_max _
    rw [hzero]
    rw [ih (f hd)]
    exact Nat.max_assoc acc (f hd) (tl.foldl (fun acc' a' => Nat.max acc' (f a')) 0)

/-- Folding `Nat.max` with projection `f` over a cons list starting from `0`:
`(x :: xs).foldl (fun acc a' => Nat.max acc (f a')) 0 = Nat.max (f x) (xs.foldl ... 0)`.
This is a convenient unfolding lemma, derived from `foldl_max_eq_max_acc_foldl_zero`. -/
lemma foldl_max_cons {α : Type} (f : α → Nat) (x : α) (xs : List α) :
    (x :: xs).foldl (fun acc a' => Nat.max acc (f a')) 0 =
    Nat.max (f x) (xs.foldl (fun acc a' => Nat.max acc (f a')) 0) := by
  rw [List.foldl_cons]
  have h0 : Nat.max (0 : Nat) (f x) = f x := Nat.max_eq_right (Nat.zero_le _)
  rw [h0]
  rw [foldl_max_eq_max_acc_foldl_zero f xs (f x)]

/-- For a nonempty list, some element's projected value equals the result of folding `Nat.max`
starting from `0`. That is, the maximum is attained by some element. -/
lemma exists_mem_foldl_max_eq {α : Type} (f : α → Nat) (l : List α) (hne : l ≠ []) :
    ∃ a ∈ l, f a = l.foldl (fun acc a' => Nat.max acc (f a')) 0 := by
  induction' l with hd tl ih
  · exact absurd rfl hne
  · rw [List.foldl_cons]
    have hzero : Nat.max 0 (f hd) = f hd := Nat.zero_max _
    rw [hzero]
    rw [foldl_max_eq_max_acc_foldl_zero f tl (f hd)]
    by_cases htl : tl = []
    · subst htl
      simp
    · rcases ih htl with ⟨a, ha, haval⟩
      rw [← haval]
      by_cases hle : f hd ≤ f a
      · have hmax : Nat.max (f hd) (f a) = f a := Nat.max_eq_right hle
        rw [hmax]
        exact ⟨a, List.mem_cons_of_mem _ ha, rfl⟩
      · have hmax : Nat.max (f hd) (f a) = f hd := Nat.max_eq_left (Nat.le_of_not_le hle)
        rw [hmax]
        exact ⟨hd, by simp, rfl⟩

/-- The result of folding `Nat.max` with a projection `f` is either the initial value `init`
or the value `f v` for some element `v` in the list. This generalizes
`exists_mem_foldl_max_eq` (which requires `init = 0` and a nonempty list) to arbitrary
`init` and any list (including empty). -/
lemma foldl_max_eq_init_or_mem {α : Type} (f : α → Nat) (init : Nat) (l : List α) :
    l.foldl (fun acc a' => Nat.max acc (f a')) init = init ∨
    ∃ v ∈ l, l.foldl (fun acc a' => Nat.max acc (f a')) init = f v := by
  induction l generalizing init with
  | nil => left; simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain h | ⟨v, hv, hv_eq⟩ := ih (Nat.max init (f hd))
    · by_cases hle : init ≥ f hd
      · left
        have hmax : Nat.max init (f hd) = init := Nat.max_eq_left hle
        simpa [hmax] using h
      · right
        have hlt : f hd > init := Nat.lt_of_not_ge hle
        have hmax : Nat.max init (f hd) = f hd := Nat.max_eq_right (Nat.le_of_lt hlt)
        exact ⟨hd, List.mem_cons_self .., by simpa [hmax] using h⟩
    · right; exact ⟨v, List.mem_cons_of_mem _ hv, hv_eq⟩

/-! ### Connection between `foldl` with `Nat.max` and `argmax`

These lemmas link the result of folding `Nat.max` with a projection `f : α → Nat`
to the element chosen by `List.argmax f l`. For nonempty lists, the fold result
equals `f` applied to the `argmax` element. -/

/-- Folding `Nat.max` with projection `f` over `l` starting from `0` equals
`(Option.map f (argmax f l)).getD 0`. That is, the fold computes the maximal
value of `f` over `l` (or `0` for the empty list). -/
lemma foldl_max_eq_argmax_getD {α : Type} [DecidableEq α] (f : α → Nat) (l : List α) :
    l.foldl (fun m a => Nat.max m (f a)) 0 = (Option.map f (argmax f l)).getD 0 := by
  induction' l with a as ih
  · simp
  · rw [argmax_cons f a as]
    simp only [foldl_cons]
    have hzero : Nat.max 0 (f a) = f a := Nat.zero_max _
    rw [hzero]
    rw [foldl_max_eq_max_acc_foldl_zero f as (f a)]
    rw [ih]
    cases h : argmax f as
    · simp [h]
    · rename_i m
      simp [h]
      by_cases hlt : f a < f m
      · simp [hlt, Nat.max_eq_right (le_of_lt hlt)]
      · simp [hlt, Nat.max_eq_left (not_lt.mp hlt)]

/-- If `argmax f l = some m`, then the fold of `Nat.max` with projection `f`
over `l` starting from `0` equals `f m`. -/
lemma foldl_max_eq_of_argmax_some {α : Type} [DecidableEq α] (f : α → Nat) (l : List α) (m : α)
    (h : argmax f l = some m) : l.foldl (fun x a => Nat.max x (f a)) 0 = f m := by
  have h' := foldl_max_eq_argmax_getD f l
  rw [h] at h'
  simpa using h'

/-! ### `filterSum` and `filterCount` — sum and count over filtered lists

These definitions compute the sum (resp. count) of values obtained by applying
a function `f` to elements of `l` that satisfy a predicate `p`.

`filterSum` works over any `AddCommMonoid β`, while `filterCount` returns a `Nat`. -/

/-- Sum of `f a` over elements `a` in `l` that satisfy predicate `p`.
For `Nat`, this is equivalent to summing `map f` over the filtered list. -/
def filterSum {α β : Type} [AddCommMonoid β] (l : List α) (p : α → Bool) (f : α → β) : β :=
  (l.filter p).foldl (fun acc a => acc + f a) 0

/-- Count of elements in `l` that satisfy predicate `p`.
Equivalent to `(l.filter p).length`. -/
def filterCount {α : Type} (l : List α) (p : α → Bool) : Nat :=
  (l.filter p).length


lemma filterSum_nil {α β : Type} [AddCommMonoid β] (p : α → Bool) (f : α → β) :
    filterSum [] p f = 0 := rfl


lemma filterCount_nil {α : Type} (p : α → Bool) : filterCount [] p = 0 := rfl

/-- `filterSum` for a cons: if the head satisfies `p`, add `f x`; otherwise add `0`. -/
lemma filterSum_cons {α β : Type} [AddCommMonoid β] (x : α) (l : List α) (p : α → Bool) (f : α → β) :
    filterSum (x :: l) p f = (if p x then f x else 0) + filterSum l p f := by
  unfold filterSum
  by_cases h : p x
  · simp [h]
    have hfold : ∀ (b : β) (xs : List α),
        xs.foldl (fun acc a => acc + f a) b = b + xs.foldl (fun acc a => acc + f a) 0 := by
      intro b xs
      induction xs generalizing b with
      | nil => simp
      | cons y ys ih =>
        rw [List.foldl_cons, List.foldl_cons, zero_add]
        rw [ih (b + f y), ih (f y)]
        abel
    rw [hfold (f x) (l.filter p)]
  · simp [h]

/-- `filterCount` for a cons: counts the head if it satisfies `p`. -/
lemma filterCount_cons {α : Type} (x : α) (l : List α) (p : α → Bool) :
    filterCount (x :: l) p = (if p x then 1 else 0) + filterCount l p := by
  unfold filterCount
  by_cases h : p x
  · simp [h, add_comm]
  · simp [h]

/-! ### Foldl sum bounds elements for `Nat` lists -/

/-- For a list of `Nat`, each element is bounded above by the sum computed via `foldl (+) 0`.
Since all `Nat` elements are nonnegative, the sum of the whole list is at least each individual
element. This lemma requires that `i` is a valid index into the list. -/
lemma foldl_sum_ge_getD (l : List Nat) (i : Nat) (h : i < l.length) : l.getD i 0 ≤ List.foldl (· + ·) 0 l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    have h_foldl : List.foldl (· + ·) (0 + x) xs = x + List.foldl (· + ·) 0 xs := by
      calc
        List.foldl (· + ·) (0 + x) xs = (0 + x) + List.foldl (· + ·) 0 xs :=
          foldl_add_eq_add_foldl_zero xs (0 + x)
        _ = x + List.foldl (· + ·) 0 xs := by simp
    rw [List.foldl_cons, h_foldl]
    cases i with
    | zero =>
      simp
    | succ i' =>
      simp
      have hi' : i' < xs.length := by
        simp at h; omega
      have ih' := ih i' hi'
      exact Nat.le_trans ih' (Nat.le_add_left _ x)

/-! ### Translation invariance of foldl with additive step function -/

/-- Translation invariance of `foldl` with an additive step function:
`foldl (λ acc x => acc + f x) (a + b) l = a + foldl (λ acc x => acc + f x) b l`.
This holds for any `AddSemigroup β`. -/
lemma foldl_add_init_add {α β : Type} [AddSemigroup β] (f : α → β) (l : List α) (a b : β) :
    l.foldl (fun acc x => acc + f x) (a + b) = a + l.foldl (fun acc x => acc + f x) b := by
  induction l generalizing a b with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    simpa [add_assoc] using ih a (b + f x)

/-! ### Translating the initial accumulator through foldl with multiplication

These lemmas are the multiplicative counterparts of `foldl_add_init_add`,
`foldl_add_eq_add_foldl_zero`, and `foldl_add_self`. -/

/-- Multiplicative counterpart of `foldl_add_init_add`: factoring a multiplier out of
the initial accumulator when the step function multiplies by `f x`:
`foldl (λ acc x => acc * f x) (a * b) l = a * foldl (λ acc x => acc * f x) b l`.
This holds for any `Semigroup α`, with list elements of a possibly different type `β`. -/
lemma foldl_mul_init_mul {α β : Type} [Semigroup α] (f : β → α) (a b : α) (l : List β) :
    l.foldl (fun acc x => acc * f x) (a * b) = a * l.foldl (fun acc x => acc * f x) b := by
  induction l generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl]
    rw [mul_assoc]
    rw [ih a (b * f x)]

/-- `List.foldl (*)` distributes over multiplication of the initial accumulator:
`foldl (*) (a * b) xs = a * foldl (*) b xs`.
This is a special case of `foldl_mul_init_mul` with `f := id`. -/
lemma foldl_mul {α : Type u} [Semigroup α] (xs : List α) (a b : α) :
    List.foldl (· * ·) (a * b) xs = a * List.foldl (· * ·) b xs := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl]
    rw [mul_assoc, ih]

/-- Multiplying by the result of `List.foldl (*) 1 xs` is the same as folding
with that multiplier as the initial accumulator: `a * foldl (*) 1 xs = foldl (*) a xs`. -/
lemma foldl_mul_one {α : Type u} [Monoid α] (xs : List α) (a : α) :
    a * List.foldl (· * ·) 1 xs = List.foldl (· * ·) a xs := by
  calc
    a * List.foldl (· * ·) 1 xs = List.foldl (· * ·) (a * 1) xs := by
      rw [← foldl_mul]
    _ = List.foldl (· * ·) a xs := by simp

/-- For a `Monoid α` and a projection `f : β → α`, folding `(fun acc x => acc * f x)`
from an initial accumulator `a` equals `a` multiplied by the fold from the identity element `1`:
`foldl (λ acc x => acc * f x) a l = a * foldl (λ acc x => acc * f x) 1 l`.

This generalizes the common pattern where the accumulator can be factored out
using the monoid structure. For example, with `String` and `(++)`:
`foldl (λ s x => s ++ g x) a xs = a ++ foldl (λ s x => s ++ g x) "" xs`.
Similarly for `Nat` addition: `foldl (λ n x => n + f x) a xs = a + foldl (λ n x => n + f x) 0 xs`. -/
lemma foldl_mul_init_one {α β : Type} [Monoid α] (f : β → α) (a : α) (l : List β) :
    l.foldl (fun acc x => acc * f x) a = a * l.foldl (fun acc x => acc * f x) 1 := by
  calc
    l.foldl (fun acc x => acc * f x) a = l.foldl (fun acc x => acc * f x) (a * 1) := by simp
    _ = a * l.foldl (fun acc x => acc * f x) 1 := foldl_mul_init_mul f a 1 l

/-! ### Foldl with a combined multiplication-addition step function

These lemmas handle foldl step functions of the form `fun acc a => acc * base + f a`,
which arise naturally when converting digit sequences to numbers using Horner's method
(in any base). They show how to distribute the initial accumulator through the fold. -/

/-- General formula for folding `fun acc a => acc * base + f a` from an arbitrary start value
`x`. The result equals `base ^ |l| * x` plus the value folded from `0`:
`foldl (λ acc a => acc * base + f a) x l = base ^ l.length * x + foldl (… ) 0 l`.

This is the Horner-method distributive law: the contribution of the initial accumulator
is scaled by `base` raised to the number of steps. For example, when converting a list
of digits in base `b` to a number, this lemma shows how the initial accumulator affects
the result. -/
lemma foldl_mul_add_eq {α : Type} (base : Nat) (f : α → Nat) (x : Nat) (l : List α) :
    l.foldl (fun acc a => acc * base + f a) x = base ^ l.length * x + l.foldl (fun acc a => acc * base + f a) 0 := by
  induction' l with a l ih generalizing x
  · simp
  · simp
    rw [ih (x * base + f a)]
    have hzero : l.foldl (fun acc a' => acc * base + f a') (f a) = base ^ l.length * f a + l.foldl (fun acc a' => acc * base + f a') 0 :=
      ih (f a)
    rw [hzero]
    simp [List.length_cons, Nat.pow_succ]
    ring

/-! ### Foldl with a choice step function

These lemmas apply when the step function `f : α → α → α` always returns one of its
two arguments — i.e., `f a b = a ∨ f a b = b`. In that case, the result of `foldl f init xs`
is always either `init` or an element of `xs`.
This captures common patterns like `chooseLonger` (pick the longer string), `Nat.min`,
`Nat.max`, and any other binary selection function. -/

/-- If `f` always returns one of its two arguments, then `foldl f acc xs` is either
the initial accumulator `acc` or a member of `xs`.
This generalizes the property of selection functions like `Longest`, `Shortest`,
`Nat.min`, and `Nat.max`. -/
lemma foldl_eq_acc_or_mem_of_choice {α : Type} (f : α → α → α)
    (h_choice : ∀ a b, f a b = a ∨ f a b = b)
    (xs : List α) (acc : α) :
    (xs.foldl f acc) = acc ∨ (xs.foldl f acc) ∈ xs := by
  induction' xs with x xs ih generalizing acc
  · left; rfl
  · rw [List.foldl]
    have hstep : f acc x = acc ∨ f acc x = x := h_choice acc x
    have h := ih (f acc x)
    rcases h with (h_eq | h_mem)
    · rw [h_eq]
      rcases hstep with (hstep_eq | hstep_eq)
      · rw [hstep_eq]; left; rfl
      · rw [hstep_eq]; right; simp
    · right; exact List.mem_cons_of_mem _ h_mem

/-! ### `sumOf` — sum of a projection over a list, and foldl accumulator lemmas -/

/-- Sum of a projection `f` over a list, computed by left fold.
`sumOf f [x₁, x₂, ..., xₙ] = f x₁ + f x₂ + ... + f xₙ`. -/
def sumOf {α : Type} (f : α → Nat) (xs : List α) : Nat :=
  xs.foldl (fun acc x => acc + f x) 0

/-- Pulling the accumulator out of a foldl over addition of a projection:
`foldl (λ acc x => acc + f x) a xs = a + foldl (λ acc x => acc + f x) 0 xs`. -/
theorem foldl_add_of_proj {α : Type} (f : α → Nat) (a : Nat) (xs : List α) :
    List.foldl (fun acc x => acc + f x) a xs = a + List.foldl (fun acc x => acc + f x) 0 xs := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl, zero_add]
    rw [ih (a + f y), ih (f y), add_assoc]

/-- For foldl with max of a projection, the initial accumulator `max a 0` can be factored out:
`foldl (λ m x => max (f x) m) (max a 0) xs = max a (foldl (λ m x => max (f x) m) 0 xs)`. -/
theorem foldl_max_of_proj {α : Type} (f : α → Nat) (a : Nat) (xs : List α) :
    List.foldl (fun m x => max (f x) m) (max a 0) xs =
    max a (List.foldl (fun m x => max (f x) m) 0 xs) := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    have h_max : max (f y) (max a 0) = max (max (f y) a) 0 := by omega
    rw [h_max]
    rw [ih (max (f y) a), ih (f y)]
    omega

theorem sumOf_cons {α : Type} (f : α → Nat) (x : α) (xs : List α) :
    sumOf f (x :: xs) = f x + sumOf f xs := by
  simp only [sumOf, List.foldl, zero_add]
  exact foldl_add_of_proj f (f x) xs

end List

namespace List


/-! ### Length and non-emptiness -/

/-- If `1 ≤ l.length`, then `l ≠ []`. -/
lemma ne_nil_of_one_le_length {α : Type} (l : List α) (h : 1 ≤ l.length) : l ≠ [] :=
  List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by omega) h)

/-- If `!l.isEmpty` evaluates to `true`, then the list is non-empty.
This bridges the boolean `isEmpty` check to the propositional `l ≠ []`. -/
lemma ne_nil_of_bnot_isEmpty {α : Type u} {l : List α} (h : (!l.isEmpty) = true) : l ≠ [] := by
  intro h_eq
  rw [h_eq] at h
  simp at h

/-- If a list is non-empty (`l ≠ []`), then `l.isEmpty` evaluates to `false`.
This is the converse of `ne_nil_of_bnot_isEmpty`. -/
lemma isEmpty_eq_false_of_ne_nil {α : Type u} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l
  · exact absurd rfl h
  · simp

/-- No natural number is less than the length of an empty list.
`¬ (i < ([] : List α).length)` for any `i : Nat`. -/
lemma not_lt_length_nil {α : Type} (i : Nat) : ¬ (i < ([] : List α).length) := by
  simp

/-- If a list's length is not less than 2, then it is non-empty.
Often used with `¬ xs.length < 2` to deduce `xs ≠ []`. -/
lemma ne_nil_of_length_ge_two {α : Type u} {xs : List α} (h : ¬ xs.length < 2) : xs ≠ [] := by
  intro heq
  rw [heq] at h
  have hlen : ([] : List α).length < 2 := by
    simpa using Nat.zero_lt_two
  exact h hlen

/-- If a list's length is not positive (`¬ xs.length > 0`), then the list must be empty.
Equivalent to the contrapositive of `List.length_pos_iff_ne_nil`. -/
lemma eq_nil_of_length_not_pos {α : Type u} {xs : List α} (h : ¬ xs.length > 0) : xs = [] := by
  have hlen : xs.length = 0 := by omega
  exact List.length_eq_zero_iff.mp hlen

/-! ### Properties of `foldl min` with zero -/

/-- Folding `Nat.min` over a list starting from `0` always yields `0`,
since `0` is the minimum natural number. -/
theorem foldl_min_zero {α : Type} (l : List α) (f : α → Nat) :
    List.foldl (fun acc a => Nat.min acc (f a)) 0 l = 0 := by
  induction' l with w ws ih
  · rfl
  · rw [List.foldl_cons]
    have hzero : Nat.min 0 (f w) = 0 := Nat.min_eq_left (Nat.zero_le _)
    rw [hzero]
    exact ih

/-! ### Properties of `foldl Nat.min` with arbitrary initial value -/

/-- `foldl Nat.min init xs ≤ init` for any list `xs`. -/
lemma foldl_min_le_init (xs : List Nat) (init : Nat) : xs.foldl Nat.min init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_rfl
  | cons a as ih =>
    rw [List.foldl_cons]
    have h1 : Nat.min init a ≤ init := Nat.min_le_left _ _
    have h2 : as.foldl Nat.min (Nat.min init a) ≤ Nat.min init a := ih (Nat.min init a)
    exact le_trans h2 h1

/-- `foldl Nat.min` is monotone in the initial value. -/
lemma foldl_min_mono {a b : Nat} (h : a ≤ b) (xs : List Nat) :
    xs.foldl Nat.min a ≤ xs.foldl Nat.min b := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    have h_min : Nat.min a x ≤ Nat.min b x := by
      rw [Nat.le_min]
      exact ⟨le_trans (Nat.min_le_left _ _) h, Nat.min_le_right _ _⟩
    exact h_min

/-- If `x` appears at the head of the unfolded fold, then the fold result ≤ `x`. -/
lemma foldl_min_le_elem {init x : Nat} {xs : List Nat} (hx : x ∈ init :: xs) :
    xs.foldl Nat.min init ≤ x := by
  induction xs generalizing init with
  | nil =>
    have hx' : x = init := by simpa using hx
    simp [hx']
  | cons hd tl ih =>
    have hx' : x = init ∨ x ∈ hd :: tl := by simpa using hx
    rcases hx' with (hx_eq | hx_tl)
    · rw [hx_eq]
      exact foldl_min_le_init (hd :: tl) init
    · have h := ih hx_tl
      rw [List.foldl_cons]
      have hmono : tl.foldl Nat.min (Nat.min init hd) ≤ tl.foldl Nat.min hd :=
        foldl_min_mono (Nat.min_le_right _ _) tl
      exact le_trans hmono h

/-- If `x ∈ xs`, then `xs.foldl Nat.min init ≤ x`. -/
lemma foldl_min_le_of_mem {init x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    xs.foldl Nat.min init ≤ x :=
  foldl_min_le_elem (List.mem_cons_of_mem init hx)

/-- The result of `foldl Nat.min x xs` is either `x` or an element of `xs`. -/
lemma foldl_min_mem (x : Nat) (xs : List Nat) :
    xs.foldl Nat.min x = x ∨ xs.foldl Nat.min x ∈ xs := by
  induction xs generalizing x with
  | nil => left; rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rcases ih (Nat.min x y) with (h | h)
    · rw [h]
      by_cases hxy : x ≤ y
      · left; simp [Nat.min_eq_left hxy]
      · right; simp [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hxy))]
    · right; exact List.mem_cons_of_mem y h

/-- If `x < y` for all `y ∈ xs`, then `foldl Nat.min x xs = x`. -/
lemma foldl_min_eq_of_forall_lt {x : Nat} {xs : List Nat} (h : ∀ y ∈ xs, x < y) :
    (List.foldl Nat.min x xs) = x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hxy : x < y := h y (by simp)
    have hys : ∀ z ∈ ys, x < z := by
      intro z hz
      exact h z (by simp [hz])
    have hmin : Nat.min x y = x := Nat.min_eq_left (Nat.le_of_lt hxy)
    simp [List.foldl, hmin, ih hys]

/-- If `x ≤ y` for all `y ∈ xs`, then `foldl Nat.min x xs = x`.
This generalizes `foldl_min_eq_of_forall_lt` to the non-strict case. -/
lemma foldl_min_eq_of_forall_le {x : Nat} {xs : List Nat} (h : ∀ y ∈ xs, x ≤ y) :
    (List.foldl Nat.min x xs) = x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hxy : x ≤ y := h y (by simp)
    have hys : ∀ z ∈ ys, x ≤ z := by
      intro z hz
      exact h z (by simp [hz])
    have hmin : Nat.min x y = x := Nat.min_eq_left hxy
    simp [List.foldl, hmin, ih hys]

/-- For any list and accumulator, the foldl-min is ≤ the foldl-max.
Generalized to any `LinearOrder` with no nonempty requirement. -/
lemma foldl_min_le_foldl_max {α : Type u} [LinearOrder α] (a : α) (l : List α) :
    l.foldl min a ≤ l.foldl max a :=
  calc
    l.foldl min a ≤ a := by
      induction' l with h t ih generalizing a
      · rfl
      · rw [List.foldl_cons]
        exact le_trans (ih (min a h)) (min_le_left _ _)
    _ ≤ l.foldl max a := by
      induction' l with h t ih generalizing a
      · rfl
      · rw [List.foldl_cons]
        exact le_trans (le_max_left _ _) (ih (max a h))



/-! ### `foldl min` with cost function -/

/-- `foldl (λ n x => min n (cost x)) init l ≤ init` for any cost function `cost : α → Nat`.
Generalizes `foldl_min_le_init` which works on `List Nat` with `Nat.min` directly. -/
lemma foldl_min_cost_le_init {α : Type} (cost : α → Nat) (l : List α) (init : Nat) :
    l.foldl (λ n x => min n (cost x)) init ≤ init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons x xs ih =>
    rw [List.foldl]
    have h := ih (min init (cost x))
    exact le_trans h (Nat.min_le_left _ _)

/-- If `x ∈ l`, then `foldl (λ n y => min n (cost y)) init l ≤ cost x`.
Generalizes `foldl_min_le_of_mem` which works on `List Nat` with `Nat.min` directly. -/
lemma foldl_min_cost_le_of_mem {α : Type} (cost : α → Nat) (l : List α) (init : Nat) (x : α) (hx : x ∈ l) :
    l.foldl (λ n y => min n (cost y)) init ≤ cost x := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl]
    simp [List.mem_cons] at hx
    rcases hx with (heq | hx')
    · rw [heq]
      have h := foldl_min_cost_le_init cost ys (min init (cost y))
      exact le_trans h (Nat.min_le_right _ _)
    · exact ih (min init (cost y)) hx'

/-- If `l` is nonempty (with head `x` and tail `xs`), then the result of folding
`λ n y => min n (cost y)` over `xs` starting from `cost x` equals `cost a` for some `a ∈ x :: xs`.
This is the existence counterpart to `foldl_min_cost_le_of_mem`. -/
lemma foldl_min_cost_exists_witness {α : Type} (cost : α → Nat) (x : α) (xs : List α) :
    ∃ a ∈ (x :: xs), (xs.foldl (fun acc y => Nat.min acc (cost y)) (cost x)) = cost a := by
  induction xs generalizing x with
  | nil => exact ⟨x, by simp, rfl⟩
  | cons y ys ih =>
    rcases Nat.le_total (cost x) (cost y) with (h | h)
    · have hmin : Nat.min (cost x) (cost y) = cost x := Nat.min_eq_left h
      have hfold : (List.foldl (fun acc z => Nat.min acc (cost z)) (cost x) (y :: ys)) =
                   (List.foldl (fun acc z => Nat.min acc (cost z)) (cost x) ys) := by
        calc
          _ = (List.foldl (fun acc z => Nat.min acc (cost z)) (Nat.min (cost x) (cost y)) ys) := rfl
          _ = (List.foldl (fun acc z => Nat.min acc (cost z)) (cost x) ys) := by rw [hmin]
      rw [hfold]
      rcases ih x with ⟨a, ha, ha_eq⟩
      have ha' : a ∈ x :: y :: ys := by
        cases ha with
        | head => simp
        | tail _ ha_ys => exact .tail _ (.tail _ ha_ys)
      exact ⟨a, ha', ha_eq⟩
    · have hmin : Nat.min (cost x) (cost y) = cost y := Nat.min_eq_right h
      have hfold : (List.foldl (fun acc z => Nat.min acc (cost z)) (cost x) (y :: ys)) =
                   (List.foldl (fun acc z => Nat.min acc (cost z)) (cost y) ys) := by
        calc
          _ = (List.foldl (fun acc z => Nat.min acc (cost z)) (Nat.min (cost x) (cost y)) ys) := rfl
          _ = (List.foldl (fun acc z => Nat.min acc (cost z)) (cost y) ys) := by rw [hmin]
      rw [hfold]
      rcases ih y with ⟨a, ha, ha_eq⟩
      have ha' : a ∈ x :: y :: ys := by
        cases ha with
        | head => simp
        | tail _ ha_ys => exact .tail _ (.tail _ ha_ys)
      exact ⟨a, ha', ha_eq⟩

/-- The result of folding `λ acc x => Nat.min acc (cost x)` over `xs` starting from `init`
is either `init` (if no element's cost is smaller than `init`) or `cost x` for some `x ∈ xs`.
This generalizes `foldl_min_mem` (which is the special case `cost = id`) and is the
"equality or" counterpart to `foldl_min_cost_le_of_mem`. -/
lemma foldl_min_cost_eq_or {α : Type} (cost : α → Nat) (xs : List α) (init : Nat) :
    xs.foldl (fun acc x => Nat.min acc (cost x)) init = init ∨
    ∃ x ∈ xs, xs.foldl (fun acc x => Nat.min acc (cost x)) init = cost x := by
  induction xs generalizing init with
  | nil => left; rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rcases ih (Nat.min init (cost y)) with (h_eq | ⟨x, hx, h_eq⟩)
    · rw [h_eq]
      have h_cases : Nat.min init (cost y) = cost y ∨ Nat.min init (cost y) = init := by
        by_cases h : init ≤ cost y
        · right; exact Nat.min_eq_left h
        · left; exact Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))
      rcases h_cases with (h_cost | h_init)
      · right; exact ⟨y, by simp, h_cost⟩
      · left; exact h_init
    · right; exact ⟨x, by simp [hx], h_eq⟩



/-! ### `foldl max` lemmas -/

/-- For any starting value `x` and list `xs`, `x ≤ foldl max x xs`. -/
lemma foldl_max_ge_start {α : Type} [LinearOrder α] (x : α) (xs : List α) : x ≤ List.foldl max x xs := by
  induction xs generalizing x with
  | nil => exact le_refl x
  | cons y ys ih =>
    dsimp [List.foldl]
    have hx_max : x ≤ max x y := le_max_left _ _
    have hmax_fold : max x y ≤ List.foldl max (max x y) ys := ih (max x y)
    exact le_trans hx_max hmax_fold

/-- For any `y` in `xs`, `y ≤ foldl max x xs`. -/
lemma foldl_max_ge_mem {α : Type} [LinearOrder α] (x : α) (xs : List α) (y : α) (hy : y ∈ xs) :
    y ≤ List.foldl max x xs := by
  induction xs generalizing x y with
  | nil => simp at hy
  | cons z zs ih =>
    have hfoldl : List.foldl max x (z :: zs) = List.foldl max (max x z) zs := rfl
    rw [hfoldl]
    cases hy with
    | head _ =>
      have hz_max : z ≤ max x z := le_max_right _ _
      have hmax_fold : max x z ≤ List.foldl max (max x z) zs :=
        foldl_max_ge_start (max x z) zs
      exact le_trans hz_max hmax_fold
    | tail _ hy' =>
      exact ih (max x z) y hy'

/-- The result of `foldl max x xs` is either `x` or an element of `xs`. -/
lemma foldl_max_mem {α : Type} [LinearOrder α] (x : α) (xs : List α) :
    List.foldl max x xs = x ∨ List.foldl max x xs ∈ xs := by
  induction xs generalizing x with
  | nil => left; rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rcases ih (max x y) with (h | h)
    · rw [h]
      by_cases hxy : x ≤ y
      · right; simp [max_eq_right hxy]
      · left; simp [max_eq_left (le_of_not_le hxy)]
    · right; exact List.mem_cons_of_mem y h



/-! ### `foldl` with `⊔` (supremum) -/

/-- For any starting value `a` and list `l`, `a ≤ l.foldl (· ⊔ ·) a l`.
Generalizes `foldl_max_ge_start` from `max` (requiring `LinearOrder`) to `⊔`
(requiring only `SemilatticeSup`). -/
lemma foldl_sup_ge_init [SemilatticeSup α] (a : α) (l : List α) : a ≤ List.foldl (· ⊔ ·) a l := by
  induction l generalizing a with
  | nil => exact le_refl a
  | cons x xs ih =>
    simp only [List.foldl]
    have h1 : a ≤ a ⊔ x := le_sup_left
    have h2 : a ⊔ x ≤ List.foldl (· ⊔ ·) (a ⊔ x) xs := ih (a ⊔ x)
    exact le_trans h1 h2

/-- If `x ∈ l`, then `x ≤ l.foldl (· ⊔ ·) init l`.
Generalizes `foldl_max_ge_mem` from `max` (requiring `LinearOrder`) to `⊔`
(requiring only `SemilatticeSup`). -/
lemma foldl_sup_ge_mem [SemilatticeSup α] (init : α) {l : List α} {x : α} (hx : x ∈ l) :
    x ≤ List.foldl (· ⊔ ·) init l := by
  revert init
  induction hx with
  | head ys =>
    intro init
    simp [List.foldl]
    have h1 : x ≤ init ⊔ x := le_sup_right
    have h2 : init ⊔ x ≤ List.foldl (· ⊔ ·) (init ⊔ x) ys :=
      foldl_sup_ge_init (init ⊔ x) ys
    exact le_trans h1 h2
  | tail y hx_mem ih =>
    intro init
    simp [List.foldl]
    exact ih (init ⊔ y)

/-- The result of `l.foldl (· ⊔ ·) init l` is either `init` or an element of `l`.
Generalizes `foldl_max_mem` from `max` (requiring `LinearOrder`) to `⊔`
(still requiring `LinearOrder` due to the case-split on `≤`). -/
lemma foldl_sup_mem_or_eq [LinearOrder α] (init : α) (l : List α) :
    List.foldl (· ⊔ ·) init l = init ∨ List.foldl (· ⊔ ·) init l ∈ l := by
  induction l generalizing init with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl]
    have h := ih (init ⊔ x)
    rcases h with (h_eq | h_mem)
    · by_cases hle : init ≤ x
      · have hres : List.foldl (· ⊔ ·) (init ⊔ x) xs = x :=
          calc
            List.foldl (· ⊔ ·) (init ⊔ x) xs = init ⊔ x := h_eq
            _ = x := sup_eq_right.mpr hle
        right
        rw [hres]
        exact List.mem_cons_self x xs
      · have hxle : x ≤ init := le_of_lt (lt_of_not_ge hle)
        have hres : List.foldl (· ⊔ ·) (init ⊔ x) xs = init :=
          calc
            List.foldl (· ⊔ ·) (init ⊔ x) xs = init ⊔ x := h_eq
            _ = init := sup_eq_left.mpr hxle
        left
        exact hres
    · right
      exact List.mem_cons_of_mem x h_mem

/-- When folding `max` over `f a` for `a ∈ l` with initial value `init`,
    either some element achieves the final result, or the final result equals `init`
    and all `f a` are bounded by `init`. -/
lemma foldl_max_mapped_exists_or_all_le {α : Type} (f : α → Nat) (l : List α) (init : Nat) :
    (∃ x ∈ l, f x = l.foldl (fun acc a => max acc (f a)) init) ∨
    (l.foldl (fun acc a => max acc (f a)) init = init ∧ ∀ x ∈ l, f x ≤ init) := by
  induction' l with hd tl ih generalizing init
  · right; simp
  · rw [List.foldl]
    have ih' := ih (max init (f hd))
    rcases ih' with (h_left | h_right)
    · rcases h_left with ⟨x, hx, hxeq⟩
      left; exact ⟨x, List.mem_cons_of_mem hd hx, hxeq⟩
    · rcases h_right with ⟨heq, hle⟩
      by_cases hle' : init ≤ f hd
      · have hmax : max init (f hd) = f hd := Nat.max_eq_right hle'
        rw [hmax] at heq hle
        left; exact ⟨hd, by simp, by rw [hmax, heq]⟩
      · have hmax : max init (f hd) = init := Nat.max_eq_left (by omega)
        rw [hmax] at heq hle
        right; constructor
        · rw [hmax, heq]
        · intro x hx_mem
          cases hx_mem with
          | head => omega
          | tail _ hx_tl => exact hle x hx_tl

/-- If a list is non-empty, folding `max` over `f a` from `0` always yields a value
    achieved by some element of the list. -/
lemma foldl_max_mapped_nonempty_exists {α : Type} (f : α → Nat) (l : List α) (hne : l ≠ []) :
    ∃ x ∈ l, f x = l.foldl (fun acc a => max acc (f a)) 0 := by
  have h_cases := foldl_max_mapped_exists_or_all_le f l 0
  rcases h_cases with (⟨x, hx, hxeq⟩ | ⟨hzero, h_all_zero⟩)
  · exact ⟨x, hx, hxeq⟩
  · rcases List.exists_cons_of_ne_nil hne with ⟨hd, tl, h_eq⟩
    subst h_eq
    have hf0 : f hd = 0 := by
      have := h_all_zero hd (by simp)
      omega
    exact ⟨hd, by simp, by rw [hf0, hzero]⟩



/-! ### `listMinAbs` — minimum absolute value in a list of integers -/

/-- Minimum absolute value in a list of integers.
Returns `0` for an empty list. -/
def listMinAbs (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => (x :: xs).foldl (fun a x => min a (abs x)) (abs x)

lemma listMinAbs_nil : listMinAbs [] = 0 := rfl


end List

namespace List

/-! ### `foldl` with addition equals sum of mapped function -/

/-- `l.foldl (λ acc x => acc + f x) b = b + (l.map f).sum`.
This expresses folding addition over a list as adding the initial accumulator `b`
to the sum of the mapped function `f`. -/
lemma foldl_add_sum_eq {α β : Type} [AddCommMonoid α] (l : List β) (f : β → α) (b : α) :
    l.foldl (λ acc x => acc + f x) b = b + (l.map f).sum := by
  induction' l with x xs ih generalizing b
  · simp
  · simp [ih (b + f x), add_comm, add_left_comm, add_assoc]

/-- `l.foldl (· + ·) h = h + l.foldl (· + ·) 0` for any `AddCommMonoid α`.
This is the fundamental decomposition of `foldl` with addition: the accumulator can always be
factored out as `h + ...`. Works for `Int`, `Nat`, and any commutative additive monoid. -/
lemma foldl_add_init {α : Type u} [AddCommMonoid α] (l : List α) (h : α) :
    l.foldl (· + ·) h = h + l.foldl (· + ·) 0 := by
  induction' l with x xs ih generalizing h
  · simp
  · simp [List.foldl]
    rw [ih (h + x), ih x]
    abel

/-- `foldl` of addition decomposes: `List.foldl (λ acc x => acc + g x) a l = a + List.foldl (λ acc x => acc + g x) 0 l`.
This is the most general form: the accumulator `a` can always be factored out, leaving
the fold from `0`. Works for any `AddCommMonoid α` (including `Nat`, `Int`, `ℝ`, etc.)
and any mapped function `g : β → α`. This generalizes `foldl_add_init` (which covers `g = id`)
to any mapped function `g`. -/
lemma foldl_add_map_init {α β : Type} [AddCommMonoid α] (g : β → α) (l : List β) (a : α) :
    List.foldl (fun acc x => acc + g x) a l = a + List.foldl (fun acc x => acc + g x) 0 l := by
  induction' l with x xs ih generalizing a
  · simp
  · rw [List.foldl_cons, List.foldl_cons, zero_add]
    rw [ih (a + g x), ih (g x)]
    abel

/-- `foldl` of addition decomposes: `l.foldl (λ acc a => acc + f a) init = init + l.foldl (λ acc a => acc + f a) 0`.
This is the `Nat`-specialized version of `foldl_add_map_init`. -/
lemma foldl_add_comm_init {α : Type} (f : α → Nat) (l : List α) (init : Nat) :
    (l.foldl (fun acc a => acc + f a) init) = init + (l.foldl (fun acc a => acc + f a) 0) :=
  foldl_add_map_init (α := Nat) f l init

/-- Generalization of `foldl_add_init` and `foldl_add_map_init`: for any fold function
`f : α → β → α` that is additive in the accumulator (`f (a + b) x = f a x + b`),
the fold decomposes: `l.foldl f k = k + l.foldl f 0`.

This captures the key property behind many counting/summing fold lemmas. -/
lemma foldl_add_hom_init {α : Type u} [AddCommMonoid α] {β : Type v} (f : α → β → α)
    (h_add : ∀ a b x, f (a + b) x = f a x + b) (l : List β) (k : α) :
    l.foldl f k = k + l.foldl f 0 := by
  induction' l with h t ih generalizing k
  · simp
  · rw [List.foldl_cons, ih (f k h)]
    have hk : f k h = f 0 h + k := by
      simpa [zero_add] using h_add 0 k h
    rw [hk, List.foldl_cons, ih (f 0 h)]
    abel

/-- When the initial accumulator is `a + b`, the `a` can be factored outside the fold:
`l.foldl (λ acc x => acc + f x) (a + b) = a + l.foldl (λ acc x => acc + f x) b`. -/
lemma foldl_add_shift {α : Type} (f : α → Nat) (xs : List α) (a b : Nat) :
    List.foldl (fun acc x => acc + f x) (a + b) xs = a + List.foldl (fun acc x => acc + f x) b xs := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, add_assoc]

/-- Folding addition over a list where every element is mapped to zero leaves the accumulator
unchanged. Since `0` is the additive identity, adding zero repeatedly does nothing.
Works for any `AddCommMonoid α`. -/
lemma foldl_add_map_zero {α β : Type} [AddCommMonoid α] (k : α) (l : List β) :
    List.foldl (· + ·) k (List.map (fun _ => (0 : α)) l) = k := by
  induction l with
  | nil => rfl
  | cons _ t ih =>
    simp only [List.map_cons, List.foldl_cons, add_zero]
    exact ih

/-- Folding addition over `replicate n 0` leaves the accumulator unchanged.
This is the `replicate`-specialized version of `foldl_add_map_zero`.
Works for any `AddCommMonoid α`. -/
lemma foldl_add_replicate_zero {α : Type} [AddCommMonoid α] (k : α) (n : Nat) :
    List.foldl (· + ·) k (List.replicate n (0 : α)) = k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, add_zero, ih]

/-! ### `foldl` with multiplication -/

/-- Factoring the left multiplier out of a `foldl` with multiplication.
`(l.foldl (· * ·) (a * b)) = a * (l.foldl (· * ·) b)`.
This holds in any `Semigroup` (only associativity needed, no commutativity).
This is more general than `foldl_mul_eq` (which requires `CommSemiring`). -/
lemma foldl_mul_left {α : Type u} [Semigroup α] (l : List α) (a b : α) :
    (l.foldl (· * ·) (a * b)) = a * (l.foldl (· * ·) b) := by
  induction l generalizing a b with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    rw [mul_assoc, ih a (b * x)]

/-- The initial accumulator of a `foldl` with multiplication can be factored out:
`(l.foldl (· * ·) a) = a * (l.foldl (· * ·) 1)`. -/
lemma foldl_mul_acc {α : Type u} [Monoid α] (l : List α) (a : α) :
    (l.foldl (· * ·) a) = a * (l.foldl (· * ·) 1) := by
  calc
    (l.foldl (· * ·) a) = (l.foldl (· * ·) (a * 1)) := by simp
    _ = a * (l.foldl (· * ·) 1) := by rw [foldl_mul_left l a 1]

/-- Folding multiplication over `(x :: xs).take (i + 1)` starting from `1` equals
`x` multiplied by the fold over `xs.take i`.
This is the multiplicative counterpart of `foldl_take_succ_cons` for addition. -/
lemma foldl_mul_take_succ_cons {α : Type u} [Monoid α] (x : α) (xs : List α) (i : Nat) :
    ((x :: xs).take (i + 1)).foldl (· * ·) 1 = x * ((xs.take i).foldl (· * ·) 1) := by
  calc
    ((x :: xs).take (i + 1)).foldl (· * ·) 1
        = (x :: (xs.take i)).foldl (· * ·) 1 := by simp
    _ = (xs.take i).foldl (· * ·) x := by simp
    _ = x * ((xs.take i).foldl (· * ·) 1) := by rw [foldl_mul_acc]

/-- `foldl` with multiplication equals the initial value times the product:
`nums.foldl (· * ·) a = a * nums.prod`. Works for any `CommSemiring α`. -/
lemma foldl_mul_eq {α : Type u} [CommSemiring α] (a : α) (nums : List α) :
    nums.foldl (· * ·) a = a * nums.prod := by
  induction' nums with x xs ih generalizing a
  · simp
  · simp [List.foldl, ih, mul_comm, mul_assoc, mul_left_comm]

/-- For a commutative monoid, `foldl` with multiplication equals `foldr`:
`l.foldl (· * ·) 1 = l.foldr (· * ·) 1`.
This is the multiplicative counterpart of `foldl_add_eq_sum`. -/
lemma foldl_mul_eq_foldr_mul {α : Type u} [CommMonoid α] (l : List α) :
    l.foldl (· * ·) 1 = l.foldr (· * ·) 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [List.foldl, List.foldr, foldl_mul_acc, ih, mul_comm, mul_assoc]

/-! ### Bitwise OR fold -/

/-- Bitwise OR of all elements in a list of natural numbers.
Folds `Nat.lor` over the list starting from `0`. -/
def bitwiseOr (nums : List Nat) : Nat :=
  List.foldl (fun acc a => Nat.lor acc a) 0 nums


lemma bitwiseOr_nil : bitwiseOr [] = 0 := by
  simp [bitwiseOr]


lemma bitwiseOr_singleton (a : Nat) : bitwiseOr [a] = a := by
  simp [bitwiseOr]
  change 0 ||| a = a
  exact Nat.zero_or a

/-- Shifting the initial accumulator through `Nat.lor` distributes over `foldl`. -/
lemma foldl_lor_shift (a b : Nat) (ns : List Nat) :
    List.foldl (fun acc x => acc.lor x) (a.lor b) ns =
    a.lor (List.foldl (fun acc x => acc.lor x) b ns) := by
  induction ns generalizing a b with
  | nil => simp
  | cons m ms ih =>
    simp [List.foldl]
    rw [show (a.lor b).lor m = a.lor (b.lor m) by
      simpa using Nat.lor_assoc a b m]
    rw [ih a (b.lor m)]

/-- A `foldl` that adds a pointwise-ordered function of each element
    is monotone in both the accumulator and the function:
    if `f r ≤ g r` for all `r` and `x ≤ y`, then
    `l.foldl (λ acc r => acc + f r) x ≤ l.foldl (λ acc r => acc + g r) y`. -/
lemma foldl_add_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ r, f r ≤ g r) (x y : Nat)
    (hxy : x ≤ y) : l.foldl (fun acc r => acc + f r) x ≤ l.foldl (fun acc r => acc + g r) y := by
  induction' l with hd tl ih generalizing x y
  · exact hxy
  · simp [List.foldl]
    have hsum : x + f hd ≤ y + g hd := Nat.add_le_add hxy (h hd)
    exact ih (x + f hd) (y + g hd) hsum

/-- If each `f a` is at least 1, then folding `(λ acc a => acc + f a - 1)` from an initial
accumulator `init` is the same as `init` plus the fold from 0. -/
lemma foldl_add_sub_one_shift {α : Type} (f : α → Nat) (l : List α) (init : Nat)
    (hf : ∀ a ∈ l, 1 ≤ f a) :
    (l.foldl (fun acc a => acc + f a - 1) init) =
    init + (l.foldl (fun acc a => acc + f a - 1) 0) := by
  induction' l with x xs ih generalizing init
  · rfl
  · have hx_ge_one : 1 ≤ f x := hf x (by simp)
    have h_add_sub : init + f x - 1 = init + (f x - 1) := by
      rw [Nat.add_sub_assoc hx_ge_one init]
    have hf_xs : ∀ a ∈ xs, 1 ≤ f a := by
      intro a ha; exact hf a (by simp [ha])
    calc
      (x :: xs).foldl (fun acc a => acc + f a - 1) init
          = xs.foldl (fun acc a => acc + f a - 1) (init + f x - 1) := rfl
      _ = (init + f x - 1) + xs.foldl (fun acc a => acc + f a - 1) 0 := ih (init + f x - 1) hf_xs
      _ = (init + (f x - 1)) + xs.foldl (fun acc a => acc + f a - 1) 0 := by rw [h_add_sub]
      _ = init + ((f x - 1) + xs.foldl (fun acc a => acc + f a - 1) 0) := by omega
      _ = init + (xs.foldl (fun acc a => acc + f a - 1) (f x - 1)) := by
        rw [ih (f x - 1) hf_xs]
      _ = init + (xs.foldl (fun acc a => acc + f a - 1) (0 + f x - 1)) := by simp
      _ = init + ((x :: xs).foldl (fun acc a => acc + f a - 1) 0) := rfl

/-- Variant of `foldl_add_comm_init` for a binary function over pairs. -/
lemma foldl_add_decompose_pair {α β : Type} (f : α → β → Nat) (l : List (α × β)) (init : Nat) :
    (l.foldl (fun acc (a, b) => acc + f a b) init) = init + (l.foldl (fun acc (a, b) => acc + f a b) 0) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp [List.foldl_cons]
    rw [ih (init + f a b), ih (f a b)]
    omega

/-- Adding `b` to the result of folding addition from `a` equals folding addition from `a + b`:
`l.foldl (· + ·) a xs + b = l.foldl (· + ·) (a + b) xs`. Works for any `AddCommSemigroup`. -/
lemma foldl_add_add_right {α : Type} [AddCommSemigroup α] (xs : List α) (a b : α) :
    List.foldl (· + ·) a xs + b = List.foldl (· + ·) (a + b) xs := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, add_assoc, add_comm, add_left_comm]

/-- Distributivity of addition over `foldl`:
`foldl (· + ·) (a + b) xs = a + foldl (· + ·) b xs`.
This factors `a` out of the initial accumulator, needing only associativity (`AddSemigroup`).
Compare `foldl_add_init` which needs commutativity but factors via `0`;
this lemma is more general in typeclass assumptions. -/
lemma foldl_add_factor_acc {α : Type} [AddSemigroup α] (xs : List α) (a b : α) :
    List.foldl (· + ·) (a + b) xs = a + List.foldl (· + ·) b xs := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih, add_assoc]

/-- An algebraic identity: `(a + b) + foldl (· + ·) 0 xs = a + foldl (· + ·) b xs`.
Follows from `foldl_add_factor_acc` and `add_zero`. Needs `AddMonoid` for the zero. -/
lemma foldl_add_from_zero {α : Type} [AddMonoid α] (xs : List α) (a b : α) :
    (a + b) + List.foldl (· + ·) 0 xs = a + List.foldl (· + ·) b xs := by
  calc
    (a + b) + List.foldl (· + ·) 0 xs
        = List.foldl (· + ·) (a + b) xs := by
      rw [← foldl_add_factor_acc xs (a + b) 0, add_zero]
    _ = a + List.foldl (· + ·) b xs := by
      rw [foldl_add_factor_acc xs a b]

end List

namespace List

/-! ### Foldl with addition -/

/-- `foldl` with an additive accumulator distributes over the initial value:
`l.foldl (fun acc x => acc + g x) a = a + l.foldl (fun acc x => acc + g x) 0`.
Holds for any `AddCommMonoid M`. -/
lemma foldl_add_acc {α M : Type} [AddCommMonoid M] (g : α → M) (a : M) (l : List α) :
    l.foldl (fun acc x => acc + g x) a = a + l.foldl (fun acc x => acc + g x) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    simp
    rw [ih (a + g x), ih (g x)]
    abel

/-- Sum a list of natural numbers as rational numbers, by casting each element to `ℚ`. -/
def sumRat (l : List Nat) : ℚ :=
  (l.map (fun n => (n : ℚ))).sum


lemma sumRat_nil : sumRat ([] : List Nat) = (0 : ℚ) := rfl


lemma sumRat_cons (x : Nat) (xs : List Nat) : sumRat (x :: xs) = (x : ℚ) + sumRat xs := by
  simp [sumRat]

end List

namespace List


/-! ### `foldlWithPrev` — fold tracking the previous element -/

/-- Fold over a list while tracking the previous element.
`foldlWithPrev f prev acc [x₁, x₂, ..., xₙ]` computes
`f xₙ₋₁ xₙ (... (f x₁ x₂ (f prev x₁ acc)))`, i.e., a left fold
where the function receives both the previous and current element
along with the accumulator. -/
def foldlWithPrev {α β : Type} (f : α → α → β → β) (prev : α) (acc : β) : List α → β
  | []      => acc
  | y :: ys => foldlWithPrev f y (f prev y acc) ys


lemma foldlWithPrev_nil {α β : Type} (f : α → α → β → β) (prev : α) (acc : β) :
    foldlWithPrev f prev acc [] = acc := rfl

lemma foldlWithPrev_cons {α β : Type} (f : α → α → β → β) (prev : α) (acc : β) (x : α) (xs : List α) :
    foldlWithPrev f prev acc (x :: xs) = foldlWithPrev f x (f prev x acc) xs := rfl

lemma foldlWithPrev_singleton {α β : Type} (f : α → α → β → β) (prev : α) (acc : β) (x : α) :
    foldlWithPrev f prev acc [x] = f prev x acc := by
  rw [foldlWithPrev_cons, foldlWithPrev_nil]

end List

namespace List

/-! ### `foldlOption` — fold with `Option` to handle empty list -/

/-- Fold a list with a binary operation, using `Option` to handle the empty case.
Returns `none` for the empty list, `some (f a₁ (f a₂ (... (f aₙ₋₁ aₙ)...)))` otherwise. -/
def foldlOption {α : Type} (f : α → α → α) (xs : List α) : Option α :=
  xs.foldl (fun acc x =>
    match acc with
    | none => some x
    | some m => some (f m x))
  none


theorem foldlOption_nil {α : Type} (f : α → α → α) : foldlOption f ([] : List α) = none := by
  simp [foldlOption]


theorem foldlOption_singleton {α : Type} (f : α → α → α) (x : α) : foldlOption f [x] = some x := by
  simp [foldlOption]

/-- `foldlOption` returns `none` iff the input list is empty. -/
theorem foldlOption_eq_none_iff {α : Type} (f : α → α → α) (xs : List α) :
    foldlOption f xs = none ↔ xs = [] := by
  let step : Option α → α → Option α := fun opt x =>
    match opt with
    | none => some x
    | some a => some (f a x)
  have aux (l : List α) (a : α) : l.foldl step (some a) ≠ none := by
    induction l generalizing a with
    | nil => simp
    | cons x xs ih => exact ih (f a x)
  cases xs with
  | nil => simp [foldlOption]
  | cons x xs =>
    have h := aux xs x
    simpa [foldlOption, step] using h


end List

namespace List

/-! ### XOR fold over list -/

/-- XOR (exclusive OR) of all `Nat` elements in a list, using `foldr` with identity `0`.
This is the XOR analogue of `List.sum`. -/
def xor : List Nat → Nat :=
  List.foldr Nat.xor 0


theorem xor_nil : xor [] = 0 := rfl

theorem xor_singleton (x : Nat) : xor [x] = x := by
  unfold xor
  simp
  exact Nat.xor_zero x

/-- Bitwise AND of the XOR-fold of two lists.
Computes `(foldl xor 0 l1) &&& (foldl xor 0 l2)`.
This is the core operation from LeetCode 1835, used to compute the XOR sum
of all pairwise `land` of elements from two lists. -/
def xorLand (l1 l2 : List Nat) : Nat :=
  Nat.land (xor l1) (xor l2)

/-- The key identity relating `xorLand` to XOR-fold over pairwise `land`:
`(xor l1) &&& (xor l2) = xor (l1.flatMap (λ a => l2.map (λ b => a &&& b)))`. -/
theorem xorLand_eq_xor_flatMap (l1 l2 : List Nat) :
    xorLand l1 l2 = xor (l1.flatMap (fun a => l2.map (fun b => Nat.land a b))) := by
  have assoc (a b c : Nat) : Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c) := Nat.xor_assoc a b c
  have zero (a : Nat) : Nat.xor 0 a = a := Nat.zero_xor a
  have and0 (a : Nat) : Nat.land a 0 = 0 := Nat.and_zero a
  have zeroAnd (a : Nat) : Nat.land 0 a = 0 := Nat.zero_and a
  have distr (a b c : Nat) : Nat.land (Nat.xor a b) c = Nat.xor (Nat.land a c) (Nat.land b c) := Nat.and_xor_distrib_right
  have distl (a b c : Nat) : Nat.land a (Nat.xor b c) = Nat.xor (Nat.land a b) (Nat.land a c) := Nat.and_xor_distrib_left
  have app (xs ys : List Nat) : xor (xs ++ ys) = Nat.xor (xor xs) (xor ys) := by
    induction xs with
    | nil => simp [xor, zero]
    | cons x xs ih => simpa [xor, assoc] using congrArg (Nat.xor x) ih
  have land_map (a : Nat) (ys : List Nat) : Nat.land a (xor ys) = xor (ys.map (Nat.land a)) := by
    induction ys with
    | nil => simp [xor, and0]
    | cons y ys ih => simpa [xor, distl] using congrArg (Nat.xor (Nat.land a y)) ih
  induction l1 with
  | nil => simp [xorLand, xor, zeroAnd]
  | cons a xs ih =>
    simp only [List.flatMap_cons, app]
    change Nat.land (Nat.xor a (xor xs)) (xor l2) = _
    rw [distr, land_map]
    exact congrArg (Nat.xor (xor (List.map (Nat.land a) l2))) ih

/-- XOR of all `Nat` elements in a list using `foldl` (left fold).
This is the `foldl` variant of `List.xor`. For XOR, `foldl` and `foldr` give the same result
since `Nat.xor` is associative and commutative, but `foldl` is often more natural
in left-to-right algorithms. -/
def xorAll : List Nat → Nat :=
  List.foldl Nat.xor 0


theorem xorAll_nil : xorAll [] = 0 := by
  simp [xorAll]

/-- Folding XOR with an initial value equals XOR-ing that value
with the XOR-fold starting from zero. -/
theorem foldl_xor_eq_xor_foldl (a : Nat) (bs : List Nat) :
    List.foldl Nat.xor a bs = Nat.xor a (List.foldl Nat.xor 0 bs) := by
  induction bs generalizing a with
  | nil =>
    simp
    exact (Nat.xor_zero a).symm
  | cons b bs ih =>
    simp [List.foldl]
    have h0 : Nat.xor 0 b = b := Nat.zero_xor b
    rw [h0]
    rw [ih (Nat.xor a b), ih b]
    exact Nat.xor_assoc a b (List.foldl Nat.xor 0 bs)

end List

namespace List

/-! ### `foldl` with `Nat.land` and `testBit` -/

/-- Bitwise AND of all elements in a list. Returns `0` for the empty list.
For a non-empty list `hd :: tl`, computes `tl.foldl Nat.land hd`. -/
def bitwiseAnd : List Nat → Nat
  | [] => 0
  | hd :: tl => tl.foldl Nat.land hd

/-- Folding `Nat.land` over a list interacts with `testBit` as a boolean AND:
for each bit position `i`, the bit is set in the result iff it was set in the initial
accumulator `a` and in every element of the list. -/
lemma testBit_foldl_land (a : Nat) (as : List Nat) (i : Nat) :
    (as.foldl Nat.land a).testBit i = (a.testBit i && as.all (λ x => x.testBit i)) := by
  induction' as with x xs ih generalizing a
  · simp
  · simp [List.foldl, List.all_cons, ih]
    have hland : (a.land x).testBit i = (a.testBit i && x.testBit i) := by
      calc
        (a.land x).testBit i = (a &&& x).testBit i := rfl
        _ = (a.testBit i && x.testBit i) := Nat.testBit_and a x i
    rw [hland, Bool.and_assoc]

end List
