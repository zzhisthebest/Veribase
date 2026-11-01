import Mathlib

/-!
# Fast Fibonacci Pairs

A fast Fibonacci pair combinator that computes `(Fₙ, F_{n+1})` over any `Semiring α`
in O(n) time via a single linear pass. This is useful for modular Fibonacci
computation (e.g., `fibPair (α := ZMod p) n`).

Mathlib's `Nat.fib` (from `Data.Nat.Fib.Basic`) serves as the specification;
`fibPair` and `fibFast` provide efficient alternative computations, with
correctness lemmas linking them to `Nat.fib`.

We also provide `fibList k a b` which generates the first `k` terms of a
Fibonacci-like sequence starting with initial values `a, b`, along with
lemmas about its length, element access, and recurrence property.
-/

namespace Nat

/-- Fibonacci step on pairs: `(a, b) ↦ (b, a + b)`. Works over any type with addition. -/
def fibStep {α : Type} [Add α] (p : α × α) : α × α := (p.2, p.1 + p.2)

/-- Fast Fibonacci pair: computes `(Fₙ, F_{n+1})` over any `Semiring α` in O(n) time.
Uses a single linear pass rather than exponential recursion, making it suitable
for computing large Fibonacci numbers modulo a modulus (e.g., `fibPair (α := ZMod p) n`). -/
def fibPair {α : Type u} [Semiring α] : Nat → α × α
  | 0 => (0, 1)
  | k + 1 =>
    let (a, b) := fibPair k
    (b, a + b)

/-- Fast n-th Fibonacci number via the pair method. O(n) time.
A convenience wrapper around `fibPair` specialized to `Nat`. -/
def fibFast (n : Nat) : Nat := (fibPair (α := Nat) n).1

/-! ### Correctness: fast equals `Nat.fib` -/

/-- `fibPair` over `Nat` computes the same values as `Nat.fib`. -/
lemma fibPair_eq (n : Nat) : fibPair (α := Nat) n = (Nat.fib n, Nat.fib (n+1)) := by
  induction' n with k ih
  · rfl
  · rw [fibPair, ih]
    have hk : k+1+1 = k+2 := by omega
    simp [hk, ← Nat.fib_add_two, add_comm]

/-- `fibFast` matches `Nat.fib`. -/
lemma fibFast_eq_fib (n : Nat) : fibFast n = Nat.fib n := by
  simp [fibFast, fibPair_eq n]

/-! ### `fibGen` — Generalized Fibonacci with arbitrary starting values -/

/-- Generalized Fibonacci sequence with arbitrary starting values `a`, `b`.
`fibGen a b n` is the n-th term of the sequence where the first two terms are `a` and `b`
and each subsequent term is the sum of the two preceding terms. -/
def fibGen (a b : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | n+2 => fibGen a b n + fibGen a b (n+1)


lemma fibGen_zero (a b : Nat) : fibGen a b 0 = a := rfl


lemma fibGen_one (a b : Nat) : fibGen a b 1 = b := rfl

lemma fibGen_succ_succ (a b n : Nat) : fibGen a b (n+2) = fibGen a b n + fibGen a b (n+1) := rfl

/-- `fibGen 0 1 n` equals the standard Fibonacci number `Nat.fib n`. -/
lemma fibGen_zero_one (n : Nat) : fibGen 0 1 n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      simp [fibGen, Nat.fib_add_two, ih n (by omega), ih (n+1) (by omega)]

/-- Seeded Fibonacci: `fibGen` with `(Nat.fib m, Nat.fib (m+1))` computes
shifted standard Fibonacci numbers: `fibGen (Nat.fib m) (Nat.fib (m+1)) n = Nat.fib (m + n)`.
This generalizes `fibGen_zero_one` (which has `m = 0`). -/
lemma fibGen_fib_seed (m n : Nat) : fibGen (Nat.fib m) (Nat.fib (m+1)) n = Nat.fib (m + n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      calc
        fibGen (Nat.fib m) (Nat.fib (m+1)) (n+2)
            = fibGen (Nat.fib m) (Nat.fib (m+1)) n + fibGen (Nat.fib m) (Nat.fib (m+1)) (n+1) := rfl
        _ = Nat.fib (m + n) + Nat.fib (m + (n+1)) := by rw [ih n (by omega), ih (n+1) (by omega)]
        _ = Nat.fib (m + n) + Nat.fib ((m + n) + 1) := by ring
        _ = Nat.fib ((m + n) + 2) := by rw [Nat.fib_add_two]
        _ = Nat.fib (m + (n+2)) := by ring

/-- Shifting the initial pair by one step shifts the entire sequence by one index:
`fibGen b (a + b) n = fibGen a b (n + 1)`. -/
lemma fibGen_shift (a b n : Nat) : fibGen b (a + b) n = fibGen a b (n + 1) := by
  refine Nat.strong_induction_on n ?_
  intro k ih
  match k with
  | 0 => rfl
  | 1 => rfl
  | k'+2 =>
    simp [fibGen]
    rw [ih k' (by omega), ih (k' + 1) (by omega)]
    have hk : k' + 1 + 1 = k' + 2 := by omega
    rw [hk, fibGen]

/-! ### `fibAux` — General Fibonacci-like list generator -/

/-- Generate the first `k` terms of a Fibonacci-like sequence starting with `a, b`,
over any type `α` with addition. `fibAux a b k` is the list `[a, b, a+b, a+2b, …]`
of length `k`. This is a general "linear recurrence" generator for any `Add`. -/
def fibAux {α : Type _} [Add α] (a b : α) (k : Nat) : List α :=
  match k with
  | 0 => []
  | k+1 => a :: fibAux b (a + b) k

lemma fibAux_length {α : Type _} [Add α] (a b : α) (k : Nat) :
    (fibAux a b k).length = k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp [fibAux, ih]

lemma fibAux_get0 {α : Type _} [Add α] [Inhabited α] (a b : α) (k : Nat) (hk : 0 < k) :
    (fibAux a b k)[0]! = a := by
  cases k
  · omega
  · simp [fibAux]

lemma fibAux_get1 {α : Type _} [Add α] [Inhabited α] (a b : α) (k : Nat) (hk : 1 < k) :
    (fibAux a b k)[1]! = b := by
  cases k
  · omega
  · rename_i k
    cases k
    · omega
    · simp [fibAux]

lemma fibAux_getElem?_zero {α : Type _} [Add α] (a b : α) (k : Nat) (hk : 0 < k) :
    (fibAux a b k)[0]? = some a := by
  cases k
  · omega
  · simp [fibAux]

lemma fibAux_getElem?_one {α : Type _} [Add α] (a b : α) (k : Nat) (hk : 1 < k) :
    (fibAux a b k)[1]? = some b := by
  cases k
  · omega
  · rename_i k
    cases k
    · omega
    · simp [fibAux]

lemma fibAux_getElem?_two {α : Type _} [Add α] (a b : α) (k : Nat) (hk : 2 < k) :
    (fibAux a b k)[2]? = some (a + b) := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | n+3 => simp [fibAux, fibAux_getElem?_one b (a+b) (n+2) (by omega)]

lemma fibAux_recurrence_getElem? {α : Type _} [AddCommSemigroup α] (a b : α) (k i : Nat) (hi : i + 2 < k) :
    (fibAux a b k)[i+2]? =
    ((fibAux a b k)[i+1]? >>= fun x =>
     (fibAux a b k)[i]? >>= fun y => some (x + y)) := by
  induction k generalizing a b i with
  | zero => omega
  | succ k ih =>
    match i with
    | 0 =>
      have hk0 : 0 < k + 1 := by omega
      have h1 : (fibAux b (a + b) k)[1]? = some (a + b) :=
        fibAux_getElem?_one b (a + b) k (by omega)
      simp [fibAux, List.getElem?_cons_succ, List.getElem?_cons_zero,
        h1, fibAux_getElem?_zero a b (k+1) hk0, fibAux_getElem?_zero b (a+b) k (by omega)]
      rw [add_comm]
    | j+1 =>
      have hjk : j + 2 < k := by omega
      simp [fibAux, List.getElem?_cons_succ, ih b (a+b) j hjk]

/-- Shifting the seeds one step shifts every element index by 1:
`(fibAux a b (k+1))[i+1]! = (fibAux b (a+b) k)[i]!`. -/
lemma fibAux_getElem!_succ {α : Type _} [Add α] [Inhabited α] (a b : α) (k i : Nat) :
    (fibAux a b (k+1))[i+1]! = (fibAux b (a + b) k)[i]! := by
  simp [fibAux]

lemma fibAux_recurrence {α : Type _} [AddCommSemigroup α] [Inhabited α] (a b : α) (k i : Nat)
    (hi : i + 2 < k) :
    (fibAux a b k)[i+2]! = (fibAux a b k)[i+1]! + (fibAux a b k)[i]! := by
  induction k generalizing a b i with
  | zero => omega
  | succ k ih =>
    match i with
    | 0 =>
      match k with
      | 0 => omega
      | 1 => omega
      | Nat.succ (Nat.succ m) => simp [fibAux, add_comm]
    | j+1 =>
      have hjk : j + 2 < k := by omega
      simpa [fibAux] using ih b (a + b) j hjk

  /-- If `f : Nat → α` satisfies the Fibonacci recurrence `f n + f (n+1) = f (n+2)`,
  then `fibAux` seeded with `f start` and `f (start+1)` correctly computes
  `f (start + i)` at index `i` (for `i < k`).
  This generalizes `fibList_spec` to any `AddCommSemigroup α`. -/
  lemma fibAux_spec_of_recurrence {α : Type u} [AddCommSemigroup α] [Inhabited α]
      (f : Nat → α) (h_recurrence : ∀ n, f n + f (n+1) = f (n+2))
      (k start i : Nat) (hi : i < k) :
      (fibAux (f start) (f (start+1)) k)[i]! = f (start + i) := by
    induction' k with m ih generalizing start i
    · exact (Nat.not_lt_zero _ hi).elim
    · simp only [fibAux]
      rw [h_recurrence start]
      rcases i with (rfl | i)
      · simp
      · have hi' : i < m := by omega
        have hi_eq := ih (start+1) i hi'
        simpa [add_comm, add_assoc, add_left_comm] using hi_eq

/-! ### `fibList` — `Nat`-specialized Fibonacci-like list generation

`fibList` is the curried `Nat`-specialized version of `fibAux` for convenient
partial application: `fibList k a b = fibAux a b k`. -/

/-- Generate the first `k` terms of a Fibonacci-like sequence starting with `a, b`.
This is the `Nat` specialization of `fibAux`: `fibList k a b = fibAux a b k`. -/
def fibList : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | k+1, a, b => a :: fibList k b (a + b)

lemma fibList_eq_fibAux (k a b : Nat) : fibList k a b = fibAux a b k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp [fibList, fibAux, ih]

/-- The length of `fibList k a b` is exactly `k`. -/
lemma fibList_length (k a b : Nat) : (fibList k a b).length = k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp [fibList, List.length_cons, ih b (a + b)]

/-- The element at index `1` of `fibList k a b` is `b`, provided `1 < k`. -/
lemma fibList_get_one (k a b : Nat) (hk : 1 < k) : (fibList k a b)[1]! = b := by
  cases k
  · omega
  · rename_i k
    have hpos : 0 < k := by omega
    rw [fibList, List.getElem!_cons_succ]
    cases k
    · omega
    · simp [fibList]

/-- The Fibonacci-like recurrence holds within `fibList`:
for indices `i` with `2 ≤ i < k`, the element at `i` equals the sum of the
two preceding elements. -/
lemma fibList_recurrence (k a b i : Nat) (h2 : 2 ≤ i) (hi : i < k) :
    (fibList k a b)[i]! = (fibList k a b)[i-1]! + (fibList k a b)[i-2]! := by
  have h := fibAux_recurrence a b k (i-2) (by omega)
  have h0 : i-2+2 = i := by omega
  have h1 : i-2+1 = i-1 := by omega
  simpa only [fibList_eq_fibAux, h0, h1] using h

/-! ### `fibList` specification

The following lemmas establish that `fibList i a b` correctly computes the
values of any function `f` that satisfies the Fibonacci recurrence
`f (n+2) = f n + f (n+1)`, given the appropriate initial values. -/

/-- If `f` satisfies the Fibonacci recurrence `f (n+2) = f n + f (n+1)`,
then `fibList i a b` with `a = f k` and `b = f (k+1)` gives `f (k + j)`
at index `j` for any `j < i`. -/
lemma fibList_spec (i k a b : Nat) (f : Nat → Nat) (ha : a = f k) (hb : b = f (k+1))
    (hrec : ∀ n, f (n+2) = f n + f (n+1)) (j : Nat) (hj : j < i) :
    (fibList i a b)[j]! = f (k + j) := by
  match i, j with
  | 0, j => exact absurd hj (Nat.not_lt_zero j)
  | i+1, 0 => simp [fibList, ha]
  | i+1, j+1 =>
    have hj' : j < i := by omega
    have hab : a + b = f (k+2) := by
      rw [ha, hb, hrec k]
    have h := fibList_spec i (k+1) b (a+b) f hb hab hrec j hj'
    simpa [fibList, add_comm, add_left_comm, add_assoc] using h
termination_by (i, j)

/-- `fibList_spec` specialized to the standard Fibonacci numbers `Nat.fib`. -/
lemma fibList_spec_fib (i k : Nat) (j : Nat) (hj : j < i) :
    (fibList i (Nat.fib k) (Nat.fib (k+1)))[j]! = Nat.fib (k + j) :=
  fibList_spec i k (Nat.fib k) (Nat.fib (k+1)) Nat.fib rfl rfl
    (fun n => by rw [Nat.fib_add_two]) j hj

/-- `fibList k` seeded with `(Nat.fib m, Nat.fib (m+1))` equals `List.ofFn` of the
shifted Fibonacci sequence: `fibList k (Nat.fib m) (Nat.fib (m+1))` is exactly
`[Nat.fib m, Nat.fib (m+1), …, Nat.fib (m+k-1)]`. -/
lemma fibList_eq_ofFn (k m : Nat) : fibList k (Nat.fib m) (Nat.fib (m+1)) =
    List.ofFn (λ (i : Fin k) => Nat.fib (m + i.val)) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [fibList, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.add_zero]
    -- goal: fibList k (Nat.fib (m+1)) (Nat.fib m + Nat.fib (m+1)) =
    --         List.ofFn fun i => Nat.fib (m + (i.val + 1))
    have hab : Nat.fib m + Nat.fib (m + 1) = Nat.fib ((m + 1) + 1) := by
      rw [← Nat.fib_add_two (n := m), show (m : Nat) + 2 = ((m : Nat) + 1) + 1 by omega]
    rw [hab, ih (m + 1)]
    congr
    funext i
    simp [add_comm, add_left_comm, add_assoc]

/-- Specialization of `fibList_eq_ofFn` for the standard `(0,1)` initial values:
`fibList n 0 1` is the list of the first `n` standard Fibonacci numbers via `List.ofFn`. -/
lemma fibList_eq_ofFn_zero (n : Nat) : fibList n 0 1 = List.ofFn (λ (j : Fin n) => Nat.fib j.val) := by
  simpa using fibList_eq_ofFn n 0

/-- The `j`-th element of `fibList k (fibGen a b i) (fibGen a b (i+1))`
is `some (fibGen a b (i + j))`, provided `j < k`.
Variant of `fibList_spec` using `getElem?` (`Option`-based) instead of `getElem!`. -/
lemma fibList_getElem?_eq (k a b i : Nat) :
    ∀ j, j < k → (fibList k (fibGen a b i) (fibGen a b (i+1)))[j]? = some (fibGen a b (i + j)) := by
  induction' k with k ih generalizing i
  · intro j hj; exact (Nat.not_lt_zero _ hj).elim
  · intro j hj
    rcases j with (rfl | j)
    · simp [fibList]
    · have hj' : j < k := by omega
      have hsum : fibGen a b i + fibGen a b (i+1) = fibGen a b (i+2) := by
        rw [fibGen_succ_succ]
      have hindex : fibGen a b ((i+1) + j) = fibGen a b (i + (j+1)) := by
        rw [show (i+1) + j = i + (j+1) by omega]
      have h_ih := ih (i+1) j hj'
      simp [fibList, h_ih, hindex, hsum]

/-- Accessing `fibList k a b` at index `i` (with `i < k`) yields `some (fibGen a b i)`.
This is the `i₀ = 0` specialization of `fibList_getElem?_eq`. -/
lemma fibList_getElem?_of_init (k a b i : Nat) (h : i < k) :
    (fibList k a b)[i]? = some (fibGen a b i) := by
  simpa [zero_add] using fibList_getElem?_eq k a b 0 i h

/-- Specialization of `fibList_getElem?_of_init` to Fibonacci seeds:
`fibList` seeded with `(Nat.fib m, Nat.fib (m+1))` yields shifted standard Fibonacci numbers. -/
lemma fibList_getElem?_fib_seed (k m i : Nat) (hi : i < k) :
    (fibList k (Nat.fib m) (Nat.fib (m+1)))[i]? = some (Nat.fib (m + i)) := by
  have h := fibList_getElem?_of_init k (Nat.fib m) (Nat.fib (m+1)) i hi
  rw [h, fibGen_fib_seed m i]

/-- The Fibonacci recurrence holds within `fibList` at every valid index,
stated in terms of `getElem?` (Option-based indexing). -/
lemma fibList_recurrence_getElem? (k a b i : Nat) (h : i + 2 < k) :
    (fibList k a b)[i+2]? = (match (fibList k a b)[i]?, (fibList k a b)[i+1]? with
                            | some x, some y => some (x + y)
                            | _, _ => none) := by
  have hi_lt_k : i < k := by omega
  have hi1_lt_k : i + 1 < k := by omega
  have hget_i : (fibList k a b)[i]? = some (fibGen a b i) := by
    simpa [zero_add] using fibList_getElem?_eq k a b 0 i hi_lt_k
  have hget_i1 : (fibList k a b)[i+1]? = some (fibGen a b (i+1)) := by
    simpa [zero_add] using fibList_getElem?_eq k a b 0 (i+1) hi1_lt_k
  have hget_i2 : (fibList k a b)[i+2]? = some (fibGen a b (i+2)) := by
    simpa [zero_add] using fibList_getElem?_eq k a b 0 (i+2) h
  rw [hget_i, hget_i1, hget_i2]
  simp [fibGen]

/-! ### `fibOne` — Fibonacci starting with F(0) = 1, F(1) = 1

This is a shifted variant of `Nat.fib`: `fibOne n = Nat.fib (n+1)`.
Commonly used in problems that define Fibonacci with initial values `(1, 1)`
rather than the standard `(0, 1)`. -/

/-- Fibonacci numbers starting with F(0) = 1, F(1) = 1.
Each subsequent term is the sum of the two preceding terms. -/
def fibOne : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => fibOne n + fibOne (n+1)

/-- `fibOne n` equals `Nat.fib (n+1)` — it is a one-index shift of the standard Fibonacci. -/
lemma fibOne_eq_fib_succ (n : Nat) : fibOne n = Nat.fib (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      simp [fibOne, Nat.fib_add_two, ih n (by omega), ih (n+1) (by omega)]

/-! ### `fibUpToFuel` — Fibonacci-like list up to a limit

Similar to `fibList` but stops early when the next value would exceed `limit`.
`fibUpToFuel fuel a b limit` generates at most `fuel` values of the sequence
`a, b, a+b, a+2b, …` where each value must be `≤ limit`. Fuel ensures termination. -/

/-- Generate at most `fuel` terms of the Fibonacci-like sequence `a,b,a+b,…` that are `≤ limit`.
Returns the list of generated values (excluding `a`, starting from `b`).
Uses fuel for structural recursion termination. -/
def fibUpToFuel (fuel : Nat) (a b limit : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel+1 =>
    if b ≤ limit then
      b :: fibUpToFuel fuel b (a + b) limit
    else
      []

/-- The length of `fibUpToFuel fuel a b limit` is at most `fuel`. -/
lemma fibUpToFuel_length_le (fuel a b limit : Nat) : (fibUpToFuel fuel a b limit).length ≤ fuel := by
  induction fuel generalizing a b with
  | zero => simp [fibUpToFuel]
  | succ fuel ih =>
    simp [fibUpToFuel]
    split <;> simp [ih]

/-- When `fibUpToFuel` is seeded with `Nat.fib m` and `Nat.fib (m+1)`, the `j`-th element
equals `Nat.fib (m+1+j)`. -/
lemma fibUpToFuel_get_fib_general (fuel m j limit : Nat)
    (hj : j < (fibUpToFuel fuel (Nat.fib m) (Nat.fib (m+1)) limit).length) :
    (fibUpToFuel fuel (Nat.fib m) (Nat.fib (m+1)) limit)[j]! = Nat.fib (m+1+j) := by
  induction fuel generalizing m j with
  | zero => simp [fibUpToFuel] at hj
  | succ fuel ih =>
    simp [fibUpToFuel] at hj ⊢
    by_cases hb : Nat.fib (m+1) ≤ limit
    · simp [hb] at hj ⊢
      cases' j with j'
      · simp
      · simp at hj ⊢
        have hsum : Nat.fib m + Nat.fib (m+1) = Nat.fib (m+2) := by
          rw [add_comm, Nat.fib_add_two, add_comm]
        rw [hsum] at hj ⊢
        have h := ih (m+1) j' hj
        simpa [show (m+1)+1+j' = m+1+(j'+1) by omega] using h
    · simp [hb] at hj

/-- Specialization of `fibUpToFuel_get_fib_general` for the standard `(0,1)` initial values. -/
lemma fibUpToFuel_get_fib_zero (fuel i limit : Nat)
    (hi : i < (fibUpToFuel fuel 0 1 limit).length) :
    (fibUpToFuel fuel 0 1 limit)[i]! = Nat.fib (i+1) := by
  have h := fibUpToFuel_get_fib_general fuel 0 i limit hi
  simpa [add_comm] using h

/-- Specification for `fibUpToFuel`: when seeded with `(Nat.fib m, Nat.fib (m+1))`, the
result `L` satisfies:
- Every element `Nat.fib (m+1+i)` for `i < L` is `≤ limit`.
- If `L < fuel` (the fuel didn't run out), then `Nat.fib (m+1+L) > limit` (next value exceeds limit).
-/
lemma fibUpToFuel_spec (fuel m limit : Nat) :
    let L := (fibUpToFuel fuel (Nat.fib m) (Nat.fib (m+1)) limit).length
    (∀ i < L, Nat.fib (m+1+i) ≤ limit) ∧ (L < fuel → Nat.fib (m+1+L) > limit) := by
  induction fuel generalizing m with
  | zero =>
    simp [fibUpToFuel]
  | succ fuel ih =>
    simp [fibUpToFuel]
    by_cases hb : Nat.fib (m+1) ≤ limit
    · simp [hb]
      have hsum : Nat.fib m + Nat.fib (m+1) = Nat.fib (m+2) := by
        rw [add_comm, Nat.fib_add_two, add_comm]
      rw [hsum]
      rcases ih (m+1) with ⟨hle, hgt⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i
        · exact hb
        · rename_i i'
          have hi' : i' < (fibUpToFuel fuel (Nat.fib (m+1)) (Nat.fib (m+2)) limit).length := by omega
          have hthis := hle i' hi'
          have h_eq : (m+1)+1+i' = m+1+(i'+1) := by omega
          rw [h_eq] at hthis
          exact hthis
      · intro hL_fuel
        have hL'_fuel : (fibUpToFuel fuel (Nat.fib (m+1)) (Nat.fib (m+2)) limit).length < fuel := by
          omega
        have this := hgt hL'_fuel
        have h_eq : (m+1)+1+(fibUpToFuel fuel (Nat.fib (m+1)) (Nat.fib (m+2)) limit).length =
                    m+1+((fibUpToFuel fuel (Nat.fib (m+1)) (Nat.fib (m+2)) limit).length + 1) := by omega
        rw [h_eq] at this
        exact this
    · have h_gt : limit < Nat.fib (m+1) := Nat.not_le.mp hb
      simp [fibUpToFuel, hb, h_gt]

/-- Specialization of `fibUpToFuel_spec` for the standard `(0,1)` initial values. -/
lemma fibUpToFuel_spec_zero (fuel limit : Nat) :
    (∀ i < (fibUpToFuel fuel 0 1 limit).length, Nat.fib (i+1) ≤ limit) ∧
    ((fibUpToFuel fuel 0 1 limit).length < fuel →
     Nat.fib ((fibUpToFuel fuel 0 1 limit).length + 1) > limit) := by
  have h := fibUpToFuel_spec fuel 0 limit
  simpa [add_comm] using h

/-! ### `n_le_fib_succ` and `fib_index_bound`

Basic inequalities about `Nat.fib` that complement the mathlib lemmas. -/

/-- `n ≤ Nat.fib (n+1)` for all natural numbers `n`. -/
lemma n_le_fib_succ (n : Nat) : n ≤ Nat.fib (n+1) := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => simp
  | 1 => decide
  | n+2 =>
    have h1 : n ≤ Nat.fib (n+1) := ih n (by omega)
    have h2 : n+1 ≤ Nat.fib (n+2) := ih (n+1) (by omega)
    by_cases hn0 : n = 0
    · subst hn0; norm_num [Nat.fib, Nat.fib_add_two]
    · have hsum_le : Nat.fib (n+2) + Nat.fib (n+1) ≥ (n+1) + n := add_le_add h2 h1
      have h_arith : n+2 ≤ (n+1) + n := by omega
      have h_fib_eq : Nat.fib (n+2+1) = Nat.fib (n+1) + Nat.fib (n+2) := by
        have h_eq : n+2+1 = (n+1)+2 := by omega
        rw [h_eq, Nat.fib_add_two]
      rw [h_fib_eq]
      calc
        n+2 ≤ (n+1) + n := h_arith
        _ ≤ Nat.fib (n+2) + Nat.fib (n+1) := hsum_le
        _ = Nat.fib (n+1) + Nat.fib (n+2) := add_comm _ _

/-- If `L ≤ limit + 1` and whenever `L < limit + 1` we have `Nat.fib (L+1) > limit`,
then any `n` with `Nat.fib (n+1) ≤ limit` must satisfy `n < L`. -/
lemma fib_index_bound {L limit n : Nat} (hL_le : L ≤ limit + 1)
    (h_gt : L < limit + 1 → Nat.fib (L+1) > limit) (hn : Nat.fib (n+1) ≤ limit) : n < L := by
  by_cases hL_lt : L < limit + 1
  · have h_fib_gt : Nat.fib (L+1) > limit := h_gt hL_lt
    by_contra! hge
    have h_le : L+1 ≤ n+1 := by omega
    have h_fib_ge : Nat.fib (n+1) ≥ Nat.fib (L+1) := Nat.fib_mono h_le
    omega
  · have hL_eq : L = limit + 1 := by omega
    rw [hL_eq]
    have hn_le_limit : n ≤ limit := by
      have : n ≤ Nat.fib (n+1) := n_le_fib_succ n
      omega
    omega

/-! ### Crossing point: where `Nat.fib` exceeds a bound

For any bound, if `Nat.fib` eventually exceeds it, there is a unique first index
`n` where `Nat.fib n ≤ bound < Nat.fib (n+1)`. These lemmas characterize that crossing. -/

/-- If `Nat.fib` eventually exceeds `bound` (i.e., `∃ m, Nat.fib m > bound`),
then there exists an index `n` such that `Nat.fib n ≤ bound` and `Nat.fib (n+1) > bound`.
This is the "crossing point" lemma for the Fibonacci sequence. -/
lemma fib_crosses_bound (bound : Nat) (hbound : ∃ m, Nat.fib m > bound) :
    ∃ n : Nat, Nat.fib n ≤ bound ∧ Nat.fib (n + 1) > bound := by
  obtain ⟨m, hm⟩ := hbound
  have hm_pos : 0 < m := by
    by_contra! h
    have hm0 : m = 0 := by omega
    subst hm0
    simp at hm
  have h_exists : ∃ k, Nat.fib (k + 1) > bound := ⟨m - 1, by
    have : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
    rwa [this]⟩
  set n := Nat.find h_exists with hn_def
  have hn : Nat.fib (n + 1) > bound := Nat.find_spec h_exists
  have hn_min : ∀ k, k < n → ¬ (Nat.fib (k + 1) > bound) := λ k hk => Nat.find_min h_exists hk
  have hn_fib_le : Nat.fib n ≤ bound := by
    by_cases hn0 : n = 0
    · rw [hn0]; simp
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn1_lt_n : n - 1 < n := by omega
      have not_gt : ¬ (Nat.fib ((n - 1) + 1) > bound) := hn_min (n - 1) hn1_lt_n
      rw [Nat.sub_add_cancel hn_pos] at not_gt
      omega
  exact ⟨n, hn_fib_le, hn⟩

/-- Uniqueness of the crossing index. If we have:
- `h_bound` : for all `i < m`, `Nat.fib (k + i) ≤ bound`
- `h_next` : `Nat.fib (k + m) > bound`
- `hn_le` : `Nat.fib (k + n) ≤ bound`
- `hn_gt` : `Nat.fib (k + n + 1) > bound`
then `m = n + 1`. That is, the first index beyond the crossing point is uniquely determined. -/
lemma fib_crossing_index_unique {m n k bound : Nat}
    (h_bound : ∀ i, i < m → Nat.fib (k + i) ≤ bound)
    (h_next : Nat.fib (k + m) > bound)
    (hn_le : Nat.fib (k + n) ≤ bound) (hn_gt : Nat.fib (k + n + 1) > bound) :
    m = n + 1 := by
  have hm_ge_np1 : n + 1 ≤ m := by
    by_contra! hlt
    have hm_le_n : m ≤ n := by omega
    have hfib_m_le_fib_n : Nat.fib (k + m) ≤ Nat.fib (k + n) :=
      Nat.fib_mono (Nat.add_le_add_left hm_le_n k)
    have hfib_m_le_bound : Nat.fib (k + m) ≤ bound :=
      Nat.le_trans hfib_m_le_fib_n hn_le
    omega
  have hm_le_np1 : m ≤ n + 1 := by
    by_contra! hgt
    have hn1_lt_m : n + 1 < m := by omega
    have h_bound_n1 : Nat.fib (k + (n + 1)) ≤ bound := h_bound (n + 1) hn1_lt_m
    have h_eq : k + (n + 1) = k + n + 1 := by omega
    rw [h_eq] at h_bound_n1
    omega
  omega

/-- For all `n`, the Fibonacci number `Nat.fib (n+2)` is strictly greater than `n`.
This is a sharp inequality: `fib(2) = 1 > 0`, `fib(3) = 2 > 1`, etc. -/
lemma fib_add_two_gt (n : Nat) : Nat.fib (n + 2) > n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => simp
  | 1 => decide
  | n' + 2 =>
    have h_eq : (n' + 2) + 2 = n' + 4 := by omega
    rw [h_eq]
    have h_fib : Nat.fib (n' + 4) = Nat.fib (n' + 2) + Nat.fib (n' + 3) := by
      rw [Nat.fib_add_two (n := n' + 2)]
    rw [h_fib]
    have h_lt1 : n' < n' + 2 := by omega
    have h_lt2 : n' + 1 < n' + 2 := by omega
    have ih1 : Nat.fib (n' + 2) > n' := ih n' h_lt1
    have ih2 : Nat.fib (n' + 3) > n' + 1 := by
      have h := ih (n' + 1) h_lt2
      simpa [add_assoc] using h
    omega

/-- If `k ≥ limit + 2`, then `Nat.fib k > limit`. Useful for bounding Fibonacci
numbers when the index is known to be sufficiently larger than a threshold. -/
lemma fib_gt_of_ge_add_two (k limit : Nat) (hk : limit + 2 ≤ k) : Nat.fib k > limit := by
  rcases Nat.le.dest hk with ⟨j, hj⟩
  rw [← hj]
  have h_eq : limit + 2 + j = (limit + j) + 2 := by omega
  rw [h_eq]
  have h := fib_add_two_gt (limit + j)
  omega

/-! ### `fibAcc` — Tail-recursive Fibonacci list generator with accumulator

`fibAcc n a b acc` generates `n` terms of the Fibonacci-like sequence starting
with `a, b`, using an accumulator for tail recursion and reversing at the end.
It is algorithmically equivalent to `fibList n a b` (produces the same result)
but uses the accumulator pattern, which yields a different (often simpler)
induction structure in proofs. -/

/-- Tail-recursive Fibonacci list generator using an accumulator.
`fibAcc m a b acc` generates `m` terms starting from `a, b`, accumulating
the generated terms (in reverse) in `acc`. The final result is `acc.reverse`
concatenated with the first `m` terms of the sequence `a, b, a+b, …`.
Equivalent to `fibList m a b` when `acc = []`. -/
def fibAcc : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, acc => acc.reverse
  | m+1, a, b, acc => fibAcc m b (a + b) (a :: acc)

/-- Equivalence between `fibAcc` and `fibList`: the accumulator-based generator
concatenates `acc.reverse` with the direct-recursion `fibList` result. -/
lemma fibAcc_eq_reverse_append (m a b : Nat) (acc : List Nat) :
    fibAcc m a b acc = acc.reverse ++ fibList m a b := by
  induction' m with m ih generalizing a b acc
  · simp [fibAcc, fibList]
  · simp [fibAcc, fibList, ih]

/-- `fibAcc` with empty accumulator equals `fibList`. -/
lemma fibAcc_eq_fibList (m a b : Nat) : fibAcc m a b [] = fibList m a b := by
  simpa using fibAcc_eq_reverse_append m a b []

/-! ### `fibAcc` for arbitrary recurrence sequences

If `f : Nat → Nat` satisfies the Fibonacci recurrence `f (n+2) = f n + f (n+1)`,
then `fibAcc` seeded with `(f m, f (m+1))` and accumulator `acc` yields
`acc.reverse ++ (List.range k).map (λ i => f (m + i))`. This generalizes the
`fibAcc_spec` family to any recurrence-satisfying function. -/

/-- For any `f : Nat → Nat` satisfying the Fibonacci recurrence, `fibAcc` with seeds
`(f m, f (m+1))` produces `acc.reverse ++ (range k).map (λ i => f (m + i))`. -/
lemma fibAcc_spec_of_recurrence (f : Nat → Nat) (hrec : ∀ n, f (n + 2) = f n + f (n + 1))
    (k m : Nat) (acc : List Nat) :
    fibAcc k (f m) (f (m + 1)) acc =
    acc.reverse ++ (List.range k).map (λ i => f (m + i)) := by
  induction k generalizing m acc with
  | zero => simp [fibAcc]
  | succ k ih =>
    rw [fibAcc, ← hrec m]
    have he : m + 2 = (m + 1) + 1 := by omega
    rw [he, ih]
    simp [List.range_succ_eq_map, List.map_map, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-! ### Correctness of `fibAcc` for standard Fibonacci numbers -/

/-- Main invariant for `fibAcc` with standard Fibonacci seeds.
If `acc.reverse` already contains the first `k` Fibonacci numbers,
then after `m` more iterations, `fibAcc` produces the first `k + m` numbers. -/
lemma fibAcc_spec (m k : Nat) (acc : List Nat)
    (h : acc.reverse = (List.range k).map Nat.fib) :
    fibAcc m (Nat.fib k) (Nat.fib (k + 1)) acc = (List.range (k + m)).map Nat.fib := by
  rw [fibAcc_spec_of_recurrence Nat.fib (fun n => Nat.fib_add_two), h]
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- Special case of `fibAcc_spec`: generating `n` standard Fibonacci numbers
with empty accumulator. `fibAcc n 0 1 []` equals `(List.range n).map Nat.fib`. -/
lemma fibAcc_zero_one (n : Nat) : fibAcc n 0 1 [] = (List.range n).map Nat.fib := by
  calc
    fibAcc n 0 1 [] = fibAcc n (Nat.fib 0) (Nat.fib (0 + 1)) [] := by simp
    _ = (List.range (0 + n)).map Nat.fib := fibAcc_spec n 0 [] (by simp)
    _ = (List.range n).map Nat.fib := by simp

/-! ### `fibGo` — Iterative Fibonacci via tail recursion

`fibGo k a b` applies the Fibonacci step `(a, b) ↦ (b, a+b)` a total of `k` times
and returns the first component. Starting from `(Nat.fib i, Nat.fib (i+1))`, after
`k` steps it yields `Nat.fib (i + k)`. This is a clean tail-recursive formulation
of the classic O(n) Fibonacci algorithm, complementing `fibPair` (which returns pairs). -/

/-- Iterative Fibonacci computation via tail recursion.
`fibGo k a b` applies the Fibonacci step `(a, b) ↦ (b, a+b)` `k` times
and returns the first component of the resulting pair. -/
def fibGo (k a b : Nat) : Nat :=
  match k with
  | 0 => a
  | m+1 => fibGo m b (a+b)

/-- A single step of `fibGo`: `fibGo (k+1) a b = fibGo k b (a+b)`. -/
lemma fibGo_succ (k a b : Nat) : fibGo (k+1) a b = fibGo k b (a+b) := by
  simp [fibGo]

/-- The main invariant: starting from consecutive Fibonacci numbers `(Nat.fib i, Nat.fib (i+1))`
and iterating `k` steps via `fibGo`, we obtain `Nat.fib (i + k)`. -/
lemma fibGo_eq (k i : Nat) : fibGo k (Nat.fib i) (Nat.fib (i+1)) = Nat.fib (i + k) := by
  induction' k with m ih generalizing i
  · simp [fibGo]
  · rw [fibGo_succ]
    have h_add : Nat.fib i + Nat.fib (i+1) = Nat.fib (i+2) := by
      rw [← Nat.fib_add_two, add_comm]
    rw [h_add, ih (i+1)]
    congr 1
    omega

/-- `fibGo` with standard initial seeds `(0, 1)` equals `Nat.fib`. -/
lemma fibGo_zero_one_eq_fib (n : Nat) : fibGo n 0 1 = Nat.fib n := by
  simpa using fibGo_eq n 0

/-! ### `fibSeq` — Standard Fibonacci sequence as a list via `List.ofFn` -/

/-- Build the first `n+1` Fibonacci numbers as a list: `[F(0), F(1), ..., F(n)]`.
This is a convenience wrapper around `List.ofFn` using `Nat.fib`.
Equivalent to `fibList (n+1) 0 1`. -/
def fibSeq (n : Nat) : List Nat :=
  List.ofFn (λ (i : Fin (n+1)) => Nat.fib i.val)

/-- The length of `fibSeq n` is `n+1`. -/

lemma fibSeq_length (n : Nat) : (fibSeq n).length = n+1 := by
  simp [fibSeq]

/-- `fibSeq n` equals `fibList (n+1) 0 1` — the same sequence via the recursive generator. -/
lemma fibSeq_eq_fibList (n : Nat) : fibSeq n = fibList (n+1) 0 1 := by
  simp [fibSeq, fibList_eq_ofFn_zero]

/-! ### `fib_ge_sub_one` — lower bound on `Nat.fib` cast to `ℤ`

These lemmas bridge `Nat.fib` with `Int` comparisons, useful when Fibonacci
numbers are compared against integer thresholds (a common pattern in problems
that generate Fibonacci numbers up to a limit expressed as `Int`). -/

/-- For all `k`, `(k : ℤ) - 1 ≤ (Nat.fib k : ℤ)`. This is a weak lower bound:
Fibonacci grows at least as fast as `k-1`. Proven by strong induction using
the recurrence `Nat.fib (n+2) = Nat.fib n + Nat.fib (n+1)`. -/
lemma fib_ge_sub_one (k : Nat) : (k : Int) - 1 ≤ (Nat.fib k : Int) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | 3 => norm_num
    | k'+4 =>
      have h_rec_eq : (Nat.fib (k'+4 : Nat) : Int) =
          (Nat.fib (k'+2 : Nat) : Int) + (Nat.fib (k'+3 : Nat) : Int) := by
        have h_nat := Nat.fib_add_two (n := k'+2)
        have h1 : (k'+2 : Nat) + 2 = (k'+4 : Nat) := by omega
        have h2 : (k'+2 : Nat) + 1 = (k'+3 : Nat) := by omega
        rw [h1, h2] at h_nat
        exact_mod_cast h_nat
      rw [h_rec_eq]
      have h2' : (k'+2 : Int) - 1 ≤ (Nat.fib (k'+2 : Nat) : Int) := by
        simpa using ih (k'+2) (by omega)
      have h3' : (k'+3 : Int) - 1 ≤ (Nat.fib (k'+3 : Nat) : Int) := by
        simpa using ih (k'+3) (by omega)
      have hcalc : ((k'+4 : Nat) : Int) - 1 ≤ ((k'+2 : Int) - 1) + ((k'+3 : Int) - 1) := by
        push_cast
        omega
      have hsum : ((k'+2 : Int) - 1) + ((k'+3 : Int) - 1) ≤
                  (Nat.fib (k'+2 : Nat) : Int) + (Nat.fib (k'+3 : Nat) : Int) := by
        linarith
      exact le_trans hcalc hsum

/-- From `(k : ℤ) - 1 ≤ (Nat.fib k : ℤ)` and `(Nat.fib k : ℤ) ≤ n`,
deduce `(k : ℤ) ≤ n + 1`. This bridges the Fibonacci lower bound to an index bound
in `ℤ` comparisons. The result holds for all `n : ℤ` (no nonnegativity needed). -/
lemma fib_le_implies_index_le (n : Int) (k : Nat) (h : (Nat.fib k : Int) ≤ n) :
    (k : Int) ≤ n + 1 := by
  have h_fib_ge : (k : Int) - 1 ≤ (Nat.fib k : Int) := fib_ge_sub_one k
  omega

/-- If `(Nat.fib k : ℤ) ≤ n` with `n ≥ 0`, then `k` is bounded by `Int.toNat n + 1`
(in `ℕ`). This is the `Nat`-index version of `fib_le_implies_index_le`, converting
the `ℤ` inequality back to `ℕ`. -/
lemma fib_index_bound_of_fib_le_int (n : Int) (hn : 0 ≤ n) (k : Nat) (h : (Nat.fib k : Int) ≤ n) :
    k ≤ Int.toNat n + 1 := by
  have hineq : (k : Int) ≤ n + 1 := fib_le_implies_index_le n k h
  have hn_nat : (Int.toNat n : Int) = n := Int.toNat_of_nonneg hn
  have hgoal : (k : Int) ≤ ((Int.toNat n + 1 : Nat) : Int) := by
    push_cast
    rw [hn_nat]
    omega
  exact_mod_cast hgoal

end Nat
