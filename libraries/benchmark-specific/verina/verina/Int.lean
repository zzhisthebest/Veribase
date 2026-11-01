import Mathlib

namespace Specific

/-!
# Integer utilities

Basic predicates on `Int`.
-/

namespace Int

/-- Check whether an integer is even. -/
def isEven (n : Int) : Bool :=
  n % 2 == 0

/-- Check whether an integer is odd. -/
def isOdd (n : Int) : Bool :=
  n % 2 != 0

/--
Return the remainder-quotient pair `(r, q)` where `r = dividend % divisor`
and `q = dividend / divisor`.
-/
def remainderQuotient (dividend divisor : Int) : Int × Int :=
  (dividend % divisor, dividend / divisor)

/--
Given `d ≠ 0`, both `(x * d) / d = x` (cancellation) and
`(x * d) / d * d = x * d` (multiplying back) hold.
Useful for `simpa`-style proofs that need both facts at once.
-/
theorem mul_ediv_cancel_and_mul_eq {d x : Int} (hd : d ≠ 0) :
    (x * d) / d = x ∧ (x * d) / d * d = x * d := by
  constructor
  · exact Int.mul_ediv_cancel x hd
  · rw [Int.mul_ediv_cancel x hd]

/--
`(a * b) / b * b = a * b`.  Holds for every `b` (even zero)
because `b ∣ a * b` trivially.
-/
theorem ediv_mul_cancel_mul_right (a b : Int) : (a * b) / b * b = a * b :=
  Int.ediv_mul_cancel ⟨a, mul_comm a b⟩

end Int

end Specific
