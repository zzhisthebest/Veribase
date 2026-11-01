import vericontest.Nat

namespace Nat

/-! ### Division lemmas

Lemmas about natural-number division (`Nat.div`) that do not appear in mathlib.
These are small, reusable facts extracted from competitive programming solutions
and verified to be generally useful across multiple problems.
-/

/-- If `0 < d` and `d ≤ M`, then `M ≤ M * M / d`.
This bound is useful when proving upper bounds on the results of division-based
computations: if the divisor is at most the numerator, the quotient of the
numerator squared over the divisor is at least the numerator.

Proof: `(Nat.le_div_iff_mul_le hd).mpr` reduces to `M * d ≤ M * M`,
which follows from `hdM : d ≤ M`. -/
lemma le_mul_self_div {d M : ℕ} (hd : 0 < d) (hdM : d ≤ M) : M ≤ M * M / d :=
  (Nat.le_div_iff_mul_le hd).mpr (Nat.mul_le_mul_left M hdM)

/-- If `2 ≤ n`, then `1 ≤ n / 2`. This is a common termination/convergence lemma
for divide-by-2 recursions: as long as `n` is at least 2, the quotient `n / 2` is
at least 1 (so the recursion is making nonzero progress). -/
lemma one_le_div_two_of_two_le {n : Nat} (h : 2 ≤ n) : 1 ≤ n / 2 := by omega

end Nat
