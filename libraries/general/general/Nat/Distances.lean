import general.Nat.ArithmeticCore
import general.Nat.NumberTheory

namespace Nat

/-! ### Absolute difference -/

/-- `absDiff a b` returns the absolute difference `|a - b|` as a natural number. -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- If `a ≥ b`, then `absDiff a b = a - b`. -/
lemma absDiff_eq_sub_of_ge {a b : Nat} (h : a ≥ b) : absDiff a b = a - b := by
  unfold absDiff
  by_cases hle : a ≤ b
  · have heq : a = b := Nat.le_antisymm hle h
    subst heq; simp
  · simp [hle]

/-- If `a ≤ b`, then `absDiff a b = b - a`. -/
lemma absDiff_eq_sub_of_le {a b : Nat} (h : a ≤ b) : absDiff a b = b - a := by
  unfold absDiff; simp [h]

/-- If `a < b`, then `absDiff a b = b - a`. -/
lemma absDiff_eq_sub_of_lt {a b : Nat} (h : a < b) : absDiff a b = b - a :=
  absDiff_eq_sub_of_le (Nat.le_of_lt h)

/-- Absolute difference of a number with itself is zero. -/

lemma absDiff_self (a : Nat) : absDiff a a = 0 := by
  simp [absDiff]

/-- Absolute difference is commutative: `absDiff a b = absDiff b a`. -/
lemma absDiff_comm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff
  by_cases h : a ≤ b
  · by_cases h' : b ≤ a
    · have heq : a = b := Nat.le_antisymm h h'
      subst heq; rfl
    · simp [h, h']
  · by_cases h' : b ≤ a
    · simp [h, h']
    · exfalso; exact h' (Nat.le_of_lt (Nat.lt_of_not_ge h))

/-- `absDiff a b = 0` if and only if `a = b`. -/
lemma absDiff_eq_zero_iff (a b : Nat) : absDiff a b = 0 ↔ a = b := by
  unfold absDiff
  split <;> omega

end Nat

/-! ### Absolute difference of `Int` as `Nat` -/

/-- Absolute difference of two integers, as a `Nat`.
`intAbsDiff (a, b) = |a - b|` computed via `Int.natAbs`. -/
def intAbsDiff (p : Int × Int) : Nat := Int.natAbs (p.1 - p.2)

namespace Nat

/-! ### Circular distance on a ring -/

/-- Minimum circular distance between positions `i` and `j` on a ring of size `n`.
Computes `min ((i - j) mod n) ((j - i) mod n)` using addition to avoid underflow.
For example, `circularDist 10 2 8 = 4` (distance 2→8 via shorter path: 2→1→0→9→8 = 4 steps). -/
def circularDist (n i j : Nat) : Nat :=
  Nat.min ((i + n - j) % n) ((j + n - i) % n)

end Nat

