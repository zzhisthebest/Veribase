import Frap.Inductive

/-!
# Addition theorems for Frap's `Hidden.Nat`

The `Frap.Inductive` module defines a custom `Nat` type (in `Hidden.Nat`) with
constructors `zero` and `succ`, along with basic operations and lemmas:
`add_zero`, `add_succ`, `zero_add`, `succ_add`, and `add_assoc`.

This module provides the missing commutativity lemma `add_comm` and its helper
lemmas, which are used as building blocks in inductive proofs about addition.
-/

set_option quotPrecheck false

namespace Hidden
namespace Nat

/-- `zero + a = a + zero` follows directly from `zero_add` and `add_zero`. -/
theorem zero_add_eq_add_zero (a : Nat) : zero + a = a + zero := by
  rw [zero_add, add_zero]

/-- `a + zero = zero + a` follows directly from `add_zero` and `zero_add`. -/
theorem add_zero_eq_zero_add (a : Nat) : a + zero = zero + a := by
  rw [add_zero, zero_add]

/-- `succ a + b = a + succ b` by combining `succ_add` and `add_succ`. -/
theorem succ_add_eq_add_succ (a b : Nat) : succ a + b = a + succ b := by
  rw [← succ_add, add_succ]

/-- `a + succ b = succ a + b` by combining `add_succ` and `succ_add`. -/
theorem add_succ_eq_succ_add (a b : Nat) : a + succ b = succ a + b := by
  rw [add_succ, ← succ_add]

/-- The inductive step lemma for proving `add_comm`:
if `a + b = b + a`, then `a + succ b = succ b + a`. -/
theorem add_succ_comm_step (a b : Nat) (h : a + b = b + a) : a + succ b = succ b + a := by
  rw [add_succ, h, succ_add]

/-- **Addition is commutative** for Frap's `Hidden.Nat`.
This is proven by induction on `n` using `add_succ_comm_step`. -/
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => exact add_zero_eq_zero_add m
  | succ n' ih => exact add_succ_comm_step m n' ih

/-!
# Multiplication theorems for Frap's `Hidden.Nat`

The Frap `Inductive` module defines `mul_zero` and `mul_succ` as definitional
lemmas, but leaves `mul_comm` unproven (`sorry`) and does not provide
distributivity (`mul_add`), associativity (`mul_assoc`), or identity
(`mul_one`, `one_mul`) lemmas.  This section fills those gaps.
-/

/-- A convenient form of `mul_succ` with `+` notation:
`m * succ n = m * n + m`. (Frap's `mul_succ` gives `m * succ n = add (m * n) m`;
this version unfolds `add` into `+` via `add_infix`.) -/
theorem mul_succ_infix (m n : Nat) : m * succ n = m * n + m := by
  rw [mul_succ, add_infix]

/-- `zero * n = zero` for Frap's `Hidden.Nat`. Proven by induction. -/
theorem zero_mul (n : Nat) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n' ih =>
      rw [mul_succ_infix, ih, add_zero]

/-- Left-distributivity of multiplication over addition for Frap's `Hidden.Nat`:
`m * (n + k) = m * n + m * k`. -/
theorem mul_add (m n k : Nat) : m * (n + k) = m * n + m * k := by
  induction k with
  | zero =>
      rw [add_zero, mul_zero, add_zero]
  | succ k' ih =>
      rw [add_succ, mul_succ_infix m (n + k'), ih, mul_succ_infix m k', add_assoc]

/-- Helper lemma: `a * (b * succ c) = a * (b * c) + a * b`. -/
theorem mul_mul_succ (a b c : Nat) : a * (b * succ c) = a * (b * c) + a * b := by
  rw [mul_succ_infix, mul_add]

/-- Right identity of multiplication for Frap's `Hidden.Nat`: `m * (succ zero) = m`. -/
theorem mul_one (m : Nat) : m * (succ zero) = m := by
  rw [mul_succ_infix, mul_zero, zero_add]

/-- Left identity of multiplication for Frap's `Hidden.Nat`: `(succ zero) * n = n`. -/
theorem one_mul (n : Nat) : (succ zero) * n = n := by
  induction n with
  | zero => rw [mul_zero]
  | succ n' ih =>
      rw [mul_succ_infix, ih, add_succ, add_zero]

/-- Multiplication is associative for Frap's `Hidden.Nat`: `(m * n) * k = m * (n * k)`. -/
theorem mul_assoc (m n k : Nat) : (m * n) * k = m * (n * k) := by
  induction k with
  | zero =>
      rw [mul_zero, mul_zero, mul_zero]
  | succ k' ih =>
      rw [mul_succ_infix, ih, mul_mul_succ]

end Nat
end Hidden
