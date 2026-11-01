import Mathlib
import fvapps.List.ExtremumSelection

namespace Specific

open _root_.List

namespace List

/-! ## Generic foldl with fallback and max/min via foldl -/

/-- Fold a binary operation over a list with a default value for the empty list.
For a non-empty list `x :: xs`, this is `xs.foldl op x`; for the empty list it
returns `default`. This is the generalization of `foldMaxD` and `foldMinD`. -/
def foldWithDefault (op : α → α → α) (default : α) : List α → α
  | [] => default
  | x :: xs => xs.foldl op x

/-- Maximum element of a list via `foldl max`, returning `fallback` for the
empty list. This is simpler than `List.maximum` (which returns `WithBot α`)
and works with any `Max` type without needing a `LinearOrder`. -/
def foldMaxD {α : Type} [Max α] (fallback : α) (l : List α) : α :=
  foldWithDefault max fallback l

/-- Minimum element of a list via `foldl min`, returning `fallback` for the
empty list. This is simpler than `List.minimum` (which returns `WithBot α`)
and works with any `Min` type without needing a `LinearOrder`. -/
def foldMinD {α : Type} [Min α] (fallback : α) (l : List α) : α :=
  foldWithDefault min fallback l

@[simp] theorem foldMaxD_nil [Max α] (fallback : α) : foldMaxD fallback [] = fallback := rfl

@[simp] theorem foldMinD_nil [Min α] (fallback : α) : foldMinD fallback [] = fallback := rfl

@[simp] theorem foldMaxD_singleton [Max α] (fallback x : α) : foldMaxD fallback [x] = x := rfl

@[simp] theorem foldMinD_singleton [Min α] (fallback x : α) : foldMinD fallback [x] = x := rfl

/-- Maximum element of a list via `foldl max`, returning `0` for the empty list.
This is a special case of `foldMaxD` with `0` as the fallback. -/
def listMaximum [Max α] [OfNat α 0] : List α → α :=
  foldMaxD 0

/-! ## Properties of `foldl max` and `foldl min` -/

/-- If `x` is the initial accumulator, then `foldl max` over any list
is at least `x`. In other words, folding `max` never makes the accumulator
smaller. -/
lemma le_foldl_max [LinearOrder α] (x : α) (xs : List α) :
    x ≤ xs.foldl max x := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
      exact le_trans (le_max_left x y) (ih (max x y))

/-- If `x` is the initial accumulator, then `foldl min` over any list
is at most `x`. In other words, folding `min` never makes the accumulator
larger. -/
lemma foldl_min_le [LinearOrder α] (x : α) (xs : List α) :
    xs.foldl min x ≤ x := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
      exact le_trans (ih (min x y)) (min_le_left x y)

/-- If the initial accumulator `start ≤ bound` and every list element
`x ≤ bound`, then `foldl max start xs ≤ bound`. In other words, folding
`max` preserves the upper bound. This is the direct `List.foldl max`
counterpart of `foldMaximumFrom_le_of_forall`. -/
lemma foldl_max_le_of_forall_mem_le [LinearOrder α] (start bound : α) (xs : List α)
    (hstart : start ≤ bound) (hxs : ∀ x, x ∈ xs → x ≤ bound) :
    xs.foldl max start ≤ bound := by
  induction xs generalizing start with
  | nil =>
      simpa using hstart
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le hstart (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

/-- Specialization of `foldl_max_le_of_forall_mem_le` with `start = 0`.
Common in problems where the accumulator starts at zero. -/
lemma foldl_max_zero_le_of_forall_mem_le [LinearOrder α] [Zero α] (bound : α) (xs : List α)
    (hzero : (0 : α) ≤ bound) (hxs : ∀ x, x ∈ xs → x ≤ bound) :
    xs.foldl max 0 ≤ bound :=
  foldl_max_le_of_forall_mem_le 0 bound xs hzero hxs

/-! ## Indexed folds over lists -/

/-- Fold over a list with an explicit index counter, threading a state `σ`
through the fold. The step function receives the current index, the current
state, and the current element, returning the new state.

`foldIndexedState step xs i s` folds `step` left-to-right over `xs`, starting
with index `i` and initial state `s`. For each element `x` at position `j`,
the state is updated as `step j state x`. -/
def foldIndexedState {α σ : Type} (step : Nat → σ → α → σ) :
    List α → Nat → σ → σ
  | [], _, state => state
  | x :: xs, i, state => foldIndexedState step xs (i + 1) (step i state x)

@[simp]
theorem foldIndexedState_nil {α σ : Type} (step : Nat → σ → α → σ)
    (index : Nat) (state : σ) :
    foldIndexedState step [] index state = state :=
  rfl

@[simp]
theorem foldIndexedState_cons {α σ : Type} (step : Nat → σ → α → σ)
    (x : α) (xs : List α) (index : Nat) (state : σ) :
    foldIndexedState step (x :: xs) index state =
      foldIndexedState step xs (index + 1) (step index state x) :=
  rfl

/-! ## Additive fold commutativity -/

/-- For `Nat` addition, folding with a non-zero accumulator is equivalent
to folding from zero then adding the accumulator. In other words, the
accumulator commutes with the sum because `+` is commutative:
`foldl (+) acc xs = acc + foldl (+) 0 xs`. -/
theorem foldl_add_comm_acc (xs : List Nat) (acc : Nat) :
    xs.foldl (· + ·) acc = acc + xs.foldl (· + ·) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    calc
      (x :: xs).foldl (· + ·) acc = xs.foldl (· + ·) (acc + x) := rfl
      _ = (acc + x) + xs.foldl (· + ·) 0 := ih (acc + x)
      _ = acc + (x + xs.foldl (· + ·) 0) := by rw [Nat.add_assoc]
      _ = acc + xs.foldl (· + ·) x := by rw [← ih x]
      _ = acc + (x :: xs).foldl (· + ·) 0 := by simp

/-- `foldl (· + ·) 0` is equivalent to `List.sum`. For an `AddCommMonoid`,
the left-fold and right-fold (via `List.sum`) produce the same result because
addition is commutative. -/
theorem foldl_add_zero_eq_sum {α : Type} [AddCommMonoid α] (xs : List α) :
    xs.foldl (· + ·) (0 : α) = xs.sum := by
  suffices ∀ acc, xs.foldl (· + ·) acc = acc + xs.sum by
    simpa using this 0
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro acc
      simp [ih (acc + x), add_assoc]

/-! ## `chooseGreater`: binary choice via `≥`

A generic function that picks the greater of two elements using the `≥`
relation. Unlike `max` which requires `Max`, this only needs `LE` and a
decidable `≥` relation. Useful as a step function in folds. -/

/-- Choose the greater of two elements using `a ≥ b` as the criterion.
`chooseGreater a b` returns `a` if `a ≥ b`, otherwise `b`. -/
def chooseGreater {α : Type} [LE α] [DecidableRel (fun a b : α => a ≥ b)]
    (a b : α) : α :=
  if a ≥ b then a else b

/-- If both `a` and `b` are `≤ bound`, then `chooseGreater a b ≤ bound`. -/
theorem chooseGreater_le {a b bound : Int} (ha : a ≤ bound) (hb : b ≤ bound) :
    chooseGreater a b ≤ bound := by
  unfold chooseGreater
  by_cases h : a ≥ b
  · simpa [h] using ha
  · simpa [h] using hb

/-- If `lower ≤ a` and `lower ≤ b`, then `lower ≤ chooseGreater a b`. -/
theorem le_chooseGreater {lower a b : Int} (ha : lower ≤ a) (hb : lower ≤ b) :
    lower ≤ chooseGreater a b := by
  unfold chooseGreater
  by_cases h : a ≥ b
  · simpa [h] using ha
  · simpa [h] using hb

/-- Folding `chooseGreater` over a list stays below a bound if the seed and
all elements are below that bound. -/
theorem foldl_chooseGreater_le_of_forall_mem_le
    {xs : List Int} {seed bound : Int}
    (hseed : seed ≤ bound) (hxs : ∀ x ∈ xs, x ≤ bound) :
    xs.foldl chooseGreater seed ≤ bound := by
  induction xs generalizing seed with
  | nil => simpa using hseed
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact chooseGreater_le hseed (hxs x (by simp))
      · intro y hy; exact hxs y (by simp [hy])

/-- Folding `chooseGreater` over a list stays above a lower bound if the seed
and all elements are above that lower bound. -/
theorem le_foldl_chooseGreater_of_forall_mem_le
    {xs : List Int} {seed lower : Int}
    (hseed : lower ≤ seed) (hxs : ∀ x ∈ xs, lower ≤ x) :
    lower ≤ xs.foldl chooseGreater seed := by
  induction xs generalizing seed with
  | nil => simpa using hseed
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact le_chooseGreater hseed (hxs x (by simp))
      · intro y hy; exact hxs y (by simp [hy])

/-! ## `maximumBy`: generic maximum via `chooseGreater` fold

Unlike `List.maximum` (which returns `Option α`), `maximumBy` takes an
explicit fallback value for the empty list. It uses `chooseGreater` in a
`foldl`, making it usable with only `LE` + decidable `≥` rather than
requiring a full `LinearOrder`. -/

/-- Maximum element of a list using `chooseGreater` via `foldl`.
Returns `fallback` for the empty list, otherwise the first element
updated by `chooseGreater` across the tail. -/
def maximumBy {α : Type} [LE α] [DecidableRel (fun a b : α => a ≥ b)]
    (fallback : α) : List α → α
  | [] => fallback
  | x :: xs => xs.foldl chooseGreater x

/-- If the fallback and all elements are `≤ bound`, then `maximumBy` is
bounded by `bound`. Int-specific. -/
theorem maximumBy_le_of_forall_mem_le
    (fallback : Int) (xs : List Int) {bound : Int}
    (hfallback : fallback ≤ bound) (hxs : ∀ x ∈ xs, x ≤ bound) :
    maximumBy fallback xs ≤ bound := by
  cases xs with
  | nil => simpa [maximumBy] using hfallback
  | cons x xs =>
      simp [maximumBy]
      exact foldl_chooseGreater_le_of_forall_mem_le
        (hxs x (by simp))
        (by intro y hy; exact hxs y (by simp [hy]))

/-- If the fallback and all elements are nonnegative, then `maximumBy` is
nonnegative. Int-specific. -/
theorem maximumBy_nonneg_of_forall_nonneg
    (fallback : Int) (xs : List Int)
    (hfallback : 0 ≤ fallback) (hxs : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ maximumBy fallback xs := by
  cases xs with
  | nil => simpa [maximumBy] using hfallback
  | cons x xs =>
      simp [maximumBy]
      exact le_foldl_chooseGreater_of_forall_mem_le
        (hxs x (by simp))
        (by intro y hy; exact hxs y (by simp [hy]))

/-! ## Recursive sum over any `AddMonoid`

A simple recursive sum that is structurally easier to reason about with
induction than `List.sum` (which is defined via `foldr`).  Equivalent to
`List.sum` but uses direct recursion on the list structure. -/

/-- Recursive sum of a list over any `AddMonoid`.  `foldSum [] = 0` and
`foldSum (x :: xs) = x + foldSum xs`. -/
def foldSum {α : Type} [AddMonoid α] : List α → α
  | [] => 0
  | x :: xs => x + foldSum xs

@[simp] theorem foldSum_nil {α : Type} [AddMonoid α] : foldSum ([] : List α) = 0 := rfl

@[simp] theorem foldSum_cons {α : Type} [AddMonoid α] (x : α) (xs : List α) :
    foldSum (x :: xs) = x + foldSum xs := rfl

/-- `foldSum` is equivalent to `List.sum`. -/
theorem foldSum_eq_sum {α : Type} [AddMonoid α] (l : List α) : foldSum l = List.sum l := by
  induction l with
  | nil => simp [foldSum]
  | cons x xs ih => simp [foldSum, List.sum_cons, ih]

/-! ## Sum bounded by length times maximum -/

/-- If every element of an `Int` list is ≤ `m`, then the sum via `foldSum` is
bounded by the length of the list times `m`. -/
lemma foldSum_le_length_mul_of_forall_le {l : List Int} {m : Int}
    (hle : ∀ x ∈ l, x ≤ m) : foldSum l ≤ (l.length : Int) * m := by
  induction l with
  | nil => simp [foldSum]
  | cons x xs ih =>
      have hx : x ≤ m := hle x (by simp)
      have hxs : foldSum xs ≤ (xs.length : Int) * m :=
        ih (fun y hy => hle y (by simp [hy]))
      calc
        foldSum (x :: xs) = x + foldSum xs := rfl
        _ ≤ m + (xs.length : Int) * m := by linarith
        _ = ((x :: xs).length : Int) * m := by simp; ring

/-- The sum of an `Int` list (via `foldSum`) is bounded by the length of the
list times its `listMaxD`-element. -/
lemma foldSum_le_length_mul_listMaxD {l : List Int} :
    foldSum l ≤ (l.length : Int) * listMaxD 0 l :=
  foldSum_le_length_mul_of_forall_le (fun _x hx => le_listMaxD_of_mem (α := Int) 0 hx)

/-! ## `foldlMaxWith`: fold with `max` using a score function

`foldlMaxWith score init xs` folds `max` over `xs`, where each element `x`
contributes `score x`. For example:
`foldlMaxWith score init [x₁, x₂, x₃] = max (max (max init (score x₁)) (score x₂)) (score x₃)`.
It's the max-counterpart of `sumBy`. -/

/-- Fold `max` over `score x` for each `x` in `xs`, starting from `init`. -/
def foldlMaxWith {α : Type} (score : α → Nat) (init : Nat) (xs : List α) : Nat :=
  xs.foldl (fun acc x => max acc (score x)) init

/-- Maximum of `score x` over all `x` in `xs`, returning `0` for the empty list. -/
def maxWith {α : Type} (score : α → Nat) (xs : List α) : Nat :=
  foldlMaxWith score 0 xs

/-- If the initial value `init ≤ bound` and every element's score `≤ bound`,
then the folded maximum is also `≤ bound`. -/
theorem foldlMaxWith_le_of_forall {α : Type} (score : α → Nat)
    {xs : List α} {init bound : Nat}
    (hinit : init ≤ bound) (hscore : ∀ x ∈ xs, score x ≤ bound) :
    foldlMaxWith score init xs ≤ bound := by
  induction xs generalizing init with
  | nil =>
      simpa [foldlMaxWith] using hinit
  | cons x xs ih =>
      simp only [foldlMaxWith, List.foldl_cons]
      change foldlMaxWith score (max init (score x)) xs ≤ bound
      apply ih
      · exact max_le hinit (hscore x (by simp))
      · intro y hy
        exact hscore y (by simp [hy])

/-! ## `foldMaximumFrom` and `foldMinimumFrom`: recursive accumulator min/max

These are structurally recursive folds that maintain an accumulator and
update it with `max` (or `min`) at each step. Unlike `foldl max a xs`,
the recursion is explicit, which simplifies induction proofs.

`foldMaximumFrom a [x₁, x₂, ..., xₙ] = max (max ... (max a x₁) ...) xₙ`
-/

/-- Fold `max` rightward over a list, starting from accumulator `a`.
`foldMaximumFrom a xs` computes the maximum of `a` and all elements of `xs`. -/
def foldMaximumFrom [Max α] (a : α) : List α → α
  | [] => a
  | x :: xs => foldMaximumFrom (max a x) xs

/-- Fold `min` rightward over a list, starting from accumulator `a`.
`foldMinimumFrom a xs` computes the minimum of `a` and all elements of `xs`. -/
def foldMinimumFrom [Min α] (a : α) : List α → α
  | [] => a
  | x :: xs => foldMinimumFrom (min a x) xs

@[simp] theorem foldMaximumFrom_nil [Max α] (a : α) : foldMaximumFrom a [] = a := rfl

@[simp] theorem foldMinimumFrom_nil [Min α] (a : α) : foldMinimumFrom a [] = a := rfl

/-! ## Bounds for `foldMaximumFrom` and `foldMinimumFrom` -/

section FoldMinMaxBounds

variable {α : Type*} [LinearOrder α]

lemma foldMaximumFrom_le_of_forall {xs : List α} {a bound : α}
    (ha : a ≤ bound) (hxs : ∀ x ∈ xs, x ≤ bound) :
    foldMaximumFrom a xs ≤ bound := by
  induction xs generalizing a with
  | nil =>
      simpa [foldMaximumFrom] using ha
  | cons x xs ih =>
      simp only [foldMaximumFrom]
      exact ih (max_le ha (hxs x (by simp))) (by
        intro y hy
        exact hxs y (by simp [hy]))

lemma le_foldMaximumFrom_of_forall {xs : List α} {a bound : α}
    (ha : bound ≤ a) (hxs : ∀ x ∈ xs, bound ≤ x) :
    bound ≤ foldMaximumFrom a xs := by
  induction xs generalizing a with
  | nil =>
      simpa [foldMaximumFrom] using ha
  | cons x xs ih =>
      simp only [foldMaximumFrom]
      exact ih (le_trans ha (le_max_left a x)) (by
        intro y hy
        exact hxs y (by simp [hy]))

lemma le_foldMaximumFrom_of_le_or_mem {xs : List α} {a x : α}
    (h : x ≤ a ∨ x ∈ xs) :
    x ≤ foldMaximumFrom a xs := by
  induction xs generalizing a with
  | nil =>
      rcases h with hxa | hxmem
      · simpa [foldMaximumFrom] using hxa
      · simp at hxmem
  | cons y ys ih =>
      simp only [foldMaximumFrom]
      rcases h with hxa | hxmem
      · exact ih (Or.inl (le_trans hxa (le_max_left a y)))
      · have hxmem' : x = y ∨ x ∈ ys := by
          simpa using hxmem
        rcases hxmem' with hxy | hxys
        · exact ih (Or.inl (by simp [hxy]))
        · exact ih (Or.inr hxys)

lemma foldMinimumFrom_le_of_le_or_mem {xs : List α} {a x : α}
    (h : a ≤ x ∨ x ∈ xs) :
    foldMinimumFrom a xs ≤ x := by
  induction xs generalizing a with
  | nil =>
      rcases h with hax | hxmem
      · simpa [foldMinimumFrom] using hax
      · simp at hxmem
  | cons y ys ih =>
      simp only [foldMinimumFrom]
      rcases h with hax | hxmem
      · exact ih (Or.inl (le_trans (min_le_left a y) hax))
      · have hxmem' : x = y ∨ x ∈ ys := by
          simpa using hxmem
        rcases hxmem' with hxy | hxys
        · exact ih (Or.inl (by simp [hxy]))
        · exact ih (Or.inr hxys)

lemma le_foldMinimumFrom_of_forall {xs : List α} {a bound : α}
    (ha : bound ≤ a) (hxs : ∀ x ∈ xs, bound ≤ x) :
    bound ≤ foldMinimumFrom a xs := by
  induction xs generalizing a with
  | nil =>
      simpa [foldMinimumFrom] using ha
  | cons x xs ih =>
      simp only [foldMinimumFrom]
      exact ih (le_min ha (hxs x (by simp))) (by
        intro y hy
        exact hxs y (by simp [hy]))

/-- The accumulator `a` is always ≤ the result of `foldMaximumFrom a xs`.
In other words, folding `max` never makes the accumulator smaller. -/
lemma le_foldMaximumFrom_self (a : α) (xs : List α) : a ≤ foldMaximumFrom a xs :=
  le_foldMaximumFrom_of_le_or_mem (Or.inl (le_refl a))

/-- The result of `foldMaximumFrom a xs` is either the original accumulator
`a` or an element of the list `xs`. This gives a precise characterization
of where the result lives. -/
lemma foldMaximumFrom_eq_self_or_mem (a : α) (xs : List α) :
    foldMaximumFrom a xs = a ∨ foldMaximumFrom a xs ∈ xs := by
  induction xs generalizing a with
  | nil =>
      simp [foldMaximumFrom]
  | cons x xs ih =>
      simp only [foldMaximumFrom]
      rcases ih (max a x) with h | h
      · rcases le_total a x with hax | hxa
        · right
          rw [h, max_eq_right hax]
          simp
        · left
          rw [h, max_eq_left hxa]
      · right
        simp [h]

/-- For a nonempty list, `foldMaximumFrom x xs` is a member of `x :: xs`. -/
lemma foldMaximumFrom_mem_cons (x : α) (xs : List α) :
    foldMaximumFrom x xs ∈ x :: xs := by
  rcases foldMaximumFrom_eq_self_or_mem x xs with h | h
  · simp [h]
  · simp [h]

end FoldMinMaxBounds

/-! ## `listMaximumD` and `listMinimumD`: max/min with default for empty list

These are thin wrappers around `foldMaximumFrom` / `foldMinimumFrom` that
return a `default` value for the empty list. For non-empty lists they
compute the extremum of the list elements (the default is ignored). -/

/-- Maximum of a list, returning `default` for the empty list.
For `x :: xs`, computes `foldMaximumFrom x xs`, which is the maximum of
the first element and all subsequent elements. -/
def listMaximumD [Max α] (default : α) (l : List α) : α :=
  match l with
  | [] => default
  | x :: xs => foldMaximumFrom x xs

/-- Minimum of a list, returning `default` for the empty list.
For `x :: xs`, computes `foldMinimumFrom x xs`, which is the minimum of
the first element and all subsequent elements. -/
def listMinimumD [Min α] (default : α) (l : List α) : α :=
  match l with
  | [] => default
  | x :: xs => foldMinimumFrom x xs

@[simp] theorem listMaximumD_nil [Max α] (default : α) :
    listMaximumD default [] = default := rfl

@[simp] theorem listMinimumD_nil [Min α] (default : α) :
    listMinimumD default [] = default := rfl

/-! ## Bounds for `listMaximumD` and `listMinimumD` -/

section ListMinMaxDBounds

variable {α : Type*} [LinearOrder α]

lemma listMaximumD_le_of_forall {xs : List α} {default bound : α}
    (hdefault : default ≤ bound) (hxs : ∀ x ∈ xs, x ≤ bound) :
    listMaximumD default xs ≤ bound := by
  cases xs with
  | nil => simpa [listMaximumD] using hdefault
  | cons x xs =>
      exact foldMaximumFrom_le_of_forall
        (hxs x (by simp)) (by
          intro y hy
          exact hxs y (by simp [hy]))

lemma le_listMaximumD_of_forall {xs : List α} {default bound : α}
    (hdefault : bound ≤ default) (hxs : ∀ x ∈ xs, bound ≤ x) :
    bound ≤ listMaximumD default xs := by
  cases xs with
  | nil => simpa [listMaximumD] using hdefault
  | cons x xs =>
      exact le_foldMaximumFrom_of_forall
        (hxs x (by simp)) (by
          intro y hy
          exact hxs y (by simp [hy]))

lemma mem_le_listMaximumD {default : α} {xs : List α} {x : α} (h : x ∈ xs) :
    x ≤ listMaximumD default xs := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      simp only [listMaximumD]
      have h' : x = a ∨ x ∈ xs := by
        simpa using h
      rcases h' with hxa | hx
      · exact le_foldMaximumFrom_of_le_or_mem (Or.inl (by simp [hxa]))
      · exact le_foldMaximumFrom_of_le_or_mem (Or.inr hx)

lemma listMinimumD_le_mem {default : α} {xs : List α} {x : α} (h : x ∈ xs) :
    listMinimumD default xs ≤ x := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      simp only [listMinimumD]
      have h' : x = a ∨ x ∈ xs := by
        simpa using h
      rcases h' with hxa | hx
      · exact foldMinimumFrom_le_of_le_or_mem (Or.inl (by simp [hxa]))
      · exact foldMinimumFrom_le_of_le_or_mem (Or.inr hx)

lemma listMaximumD_le_of_nonempty_subset {default : α} {xs ys : List α}
    (hne : xs ≠ []) (hsub : ∀ x ∈ xs, x ∈ ys) :
    listMaximumD default xs ≤ listMaximumD default ys := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp only [listMaximumD]
      exact foldMaximumFrom_le_of_forall
        (mem_le_listMaximumD (hsub x (by simp))) (by
          intro y hy
          exact mem_le_listMaximumD (hsub y (by simp [hy])))

lemma listMinimumD_le_of_nonempty_subset {default : α} {xs ys : List α}
    (hne : xs ≠ []) (hsub : ∀ x ∈ xs, x ∈ ys) :
    listMinimumD default ys ≤ listMinimumD default xs := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp only [listMinimumD]
      exact le_foldMinimumFrom_of_forall
        (listMinimumD_le_mem (hsub x (by simp))) (by
          intro y hy
          exact listMinimumD_le_mem (hsub y (by simp [hy])))

end ListMinMaxDBounds

/-! ## Range (max - min) inequalities -/

section ListMinMaxDRange

variable {α : Type*} [LinearOrderedAddCommGroup α]

/-- The range (max - min) of a nonempty sublist is bounded by the
range of the containing list. -/
lemma listRangeD_le_of_nonempty_subset {default : α} {xs ys : List α}
    (hne : xs ≠ []) (hsub : ∀ x ∈ xs, x ∈ ys) :
    listMaximumD default xs - listMinimumD default xs ≤
      listMaximumD default ys - listMinimumD default ys := by
  exact sub_le_sub
    (listMaximumD_le_of_nonempty_subset hne hsub)
    (listMinimumD_le_of_nonempty_subset hne hsub)

end ListMinMaxDRange

/-! ## Map invariance in folds

If a step function `step` is invariant under `f` for all elements of `xs`
(and for all possible accumulator values), then folding over the mapped list
is equal to folding over the original list.  This is especially useful when
`f` is an involution (`f ∘ f = id`) on the relevant elements and the step
function is commutative in the accumulator. -/

/-- If `step acc (f x) = step acc x` for all `x ∈ xs` and all `acc : β`,
then `foldl step acc` over `xs.map f` equals `foldl step acc` over `xs`.
In other words: mapping by `f` is a no-op for the fold because the step
function does not distinguish `f x` from `x`. -/
theorem foldl_map_eq_of_forall
    {α β : Type*} {step : β → α → β} {f : α → α} {xs : List α}
    (acc : β)
    (h : ∀ acc x, x ∈ xs → step acc (f x) = step acc x) :
    (xs.map f).foldl step acc = xs.foldl step acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      have hx : step acc (f x) = step acc x := h acc x (by simp)
      have hxs : ∀ acc y, y ∈ xs → step acc (f y) = step acc y := by
        intro acc y hy
        exact h acc y (by simp [hy])
      simp [hx, ih (step acc x) hxs]

/-! ## `indexedCombineFrom`: indexed fold with a combine operation

`indexedCombineFrom zero combine next term xs i` folds over `xs` starting from
index `i`. For each element `x` at index `idx`, it computes `term idx x` and
combines it with the accumulated result using `combine`. The empty list returns
`zero`. The index advances by `next` between elements.

This generalizes `foldIndexedState` by allowing a custom combine operation
and zero (forming a monoid-like structure), rather than threading arbitrary
user-defined state. -/

/-- Fold over a list with an index counter, combining results with a
monoid-like operation. `indexedCombineFrom zero combine next term xs i` starts
at index `i`, computes `term idx x` for each `x` at index `idx`, and combines
using `combine`, with `zero` as the base case.

Example: `indexedCombineFrom 0 (+) Nat.succ (fun i x => x * i) [a,b,c] 1`
calculates `(a*1) + (b*2) + (c*3)`. -/
def indexedCombineFrom {ι α β : Type}
    (zero : β) (combine : β → β → β) (next : ι → ι) (term : ι → α → β) :
    List α → ι → β
  | [], _ => zero
  | x :: xs, index => combine (term index x) (indexedCombineFrom zero combine next term xs (next index))

@[simp]
theorem indexedCombineFrom_nil {ι α β : Type}
    (zero : β) (combine : β → β → β) (next : ι → ι) (term : ι → α → β) (index : ι) :
    indexedCombineFrom zero combine next term [] index = zero := rfl

@[simp]
theorem indexedCombineFrom_cons {ι α β : Type}
    (zero : β) (combine : β → β → β) (next : ι → ι) (term : ι → α → β)
    (x : α) (xs : List α) (index : ι) :
    indexedCombineFrom zero combine next term (x :: xs) index =
      combine (term index x) (indexedCombineFrom zero combine next term xs (next index)) := rfl

theorem indexedCombineFrom_singleton {ι α β : Type}
    (zero : β) (combine : β → β → β) (next : ι → ι) (term : ι → α → β)
    (x : α) (index : ι)
    (hzero : combine (term index x) zero = term index x) :
    indexedCombineFrom zero combine next term [x] index = term index x := by
  simpa [indexedCombineFrom] using hzero

/-! ## `indexedSumFrom`: specialized indexed fold for `Int` addition

`indexedSumFrom` is `indexedCombineFrom` specialized to `Int` addition with
`zero = 0` and `combine = (+)`. -/

/-- Sum a term function over a list with an index counter, returning `Int`.
`indexedSumFrom next term xs i` = `∑_{j} term idx_j x_j` where `idx_0 = i`
and `idx_{j+1} = next idx_j`. -/
def indexedSumFrom {ι α : Type} (next : ι → ι) (term : ι → α → Int) :
    List α → ι → Int :=
  indexedCombineFrom 0 (fun left right => left + right) next term

@[simp]
theorem indexedSumFrom_nil {ι α : Type}
    (next : ι → ι) (term : ι → α → Int) (index : ι) :
    indexedSumFrom next term [] index = 0 := by
  simp [indexedSumFrom]

@[simp]
theorem indexedSumFrom_cons {ι α : Type}
    (next : ι → ι) (term : ι → α → Int) (x : α) (xs : List α) (index : ι) :
    indexedSumFrom next term (x :: xs) index =
      term index x + indexedSumFrom next term xs (next index) := rfl

@[simp]
theorem indexedSumFrom_singleton {ι α : Type}
    (next : ι → ι) (term : ι → α → Int) (x : α) (index : ι) :
    indexedSumFrom next term [x] index = term index x := by
  simp [indexedSumFrom]

/-! ## `sumByWith`: map-and-combine over a list

`sumByWith zero combine value xs` maps each element `x` of `xs` to `value x`
and combines the results using `combine`, with `zero` as the base case.
This is essentially `List.map` followed by a fold, but defined via
`indexedCombineFrom` with `Nat.succ` indexing (the index is ignored). -/

/-- Map each element of a list to a value, then combine the results with a
monoid-like operation. `sumByWith zero combine value [x₁, ..., xₙ]` equals
`combine (value x₁) (combine ... (combine (value xₙ) zero)...)`.
This generalizes `sumBy` to arbitrary combine operations and return types. -/
def sumByWith {α β : Type} (zero : β) (combine : β → β → β) (value : α → β)
    (xs : List α) : β :=
  indexedCombineFrom zero combine Nat.succ (fun _ x => value x) xs 0

@[simp]
theorem sumByWith_nil {α β : Type}
    (zero : β) (combine : β → β → β) (value : α → β) :
    sumByWith zero combine value [] = zero := by
  simp [sumByWith]

theorem sumByWith_singleton {α β : Type}
    (zero : β) (combine : β → β → β) (value : α → β) (x : α)
    (hzero : combine (value x) zero = value x) :
    sumByWith zero combine value [x] = value x := by
  simpa [sumByWith] using
    indexedCombineFrom_singleton zero combine Nat.succ (fun _ x => value x) x 0 hzero

/-! ## Additive value fold

`foldlAddValue` is the generic `foldl` pattern where each element is first
mapped through a `value` function and then added to the accumulator.
It is the foldl-based counterpart of `sumMap` (defined recursively in
`Aggregation.lean`). The theorems here establish that `foldlAddValue` is
invariant under permutations when the addition is commutative. -/

/-- The step function for `foldlAddValue`: `addValue value acc x = acc + value x`. -/
def addValue {α β : Type} [Add β] (value : α → β) (acc : β) (x : α) : β :=
  acc + value x

/-- Fold `addValue value` over `xs` starting from `acc`.
`foldlAddValue value acc [x₁, ..., xₙ] = acc + value x₁ + ... + value xₙ`. -/
def foldlAddValue {α β : Type} [Add β] (value : α → β) (acc : β) (xs : List α) : β :=
  xs.foldl (addValue value) acc

/-- `foldlAddValue` distributes over `List.map`:
`foldlAddValue value acc (xs.map f) = foldlAddValue (value ∘ f) acc xs`. -/
theorem foldlAddValue_map {α β γ : Type} [Add γ] (value : β → γ) (f : α → β)
    (xs : List α) (acc : γ) :
    foldlAddValue value acc (xs.map f) = foldlAddValue (value ∘ f) acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp [foldlAddValue, addValue, Function.comp_apply]
      exact ih (acc + value (f x))

/-- `addValue` is right-commutative when `β` is an `AddCommSemigroup`. -/
theorem addValue_rightCommutative {α β : Type} [AddCommSemigroup β] (value : α → β) :
    RightCommutative (addValue value) := by
  constructor
  intro acc x y
  simp [addValue, add_assoc, add_comm, add_left_comm]

/-- `foldlAddValue` is invariant under permutation of the list when addition is commutative. -/
theorem foldlAddValue_eq_of_perm {α β : Type} [AddCommSemigroup β] (value : α → β)
    {xs ys : List α} (acc : β) (h : xs.Perm ys) :
    foldlAddValue value acc xs = foldlAddValue value acc ys := by
  unfold foldlAddValue
  haveI : RightCommutative (addValue value) := addValue_rightCommutative value
  exact List.Perm.foldl_eq h acc

end List

end Specific
