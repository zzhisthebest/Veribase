import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-!
General arithmetic lemmas about `ℕ`.
-/

/--
Rearranges a nested sum of the form `2^n * (2^n * (2^n * d + c) + b) + a` into
`a + 2^n * (b + 2^n * (c + 2^n * d))`.
-/
lemma nested_two_pow_mul_add (n : ℕ) (a b c d : ℕ) :
    2^n * (2^n * (2^n * d + c) + b) + a = a + 2^n * (b + 2^n * (c + 2^n * d)) := by
  ring

namespace Nat

/--
If `b ≤ a < 2 * b`, then `a % b = a - b` (since `a / b = 1`).
-/
lemma mod_eq_sub_of_div_one {a b : ℕ} (hge : b ≤ a) (hlt : a < 2 * b) : a % b = a - b := by
  have hpos : 0 < b := by omega
  have h_div : a / b = 1 := by
    have h_lt_div : a / b < 2 := Nat.div_lt_of_lt_mul (by omega)
    have h_ge_one_div : 1 ≤ a / b := Nat.succ_le_of_lt (Nat.div_pos hge hpos)
    omega
  have h_div_mod := Nat.div_add_mod a b
  rw [h_div] at h_div_mod
  omega

/--
Twice a natural number cannot equal an odd number plus twice another natural number.
-/
lemma two_mul_ne_odd_plus_two_mul {c b p' : ℕ} (hp_odd : p' % 2 = 1) : 2 * c ≠ p' + 2 * b := by
  intro h
  have h_lhs_mod : (2 * c) % 2 = 0 := by simp
  have h_rhs_mod : (p' + 2 * b) % 2 = 1 := by
    calc
      (p' + 2 * b) % 2 = ((p' % 2) + ((2 * b) % 2)) % 2 := by rw [Nat.add_mod]
      _ = (1 + 0) % 2 := by simp [hp_odd]
      _ = 1 := by norm_num
  rw [h] at h_lhs_mod
  rw [h_rhs_mod] at h_lhs_mod
  norm_num at h_lhs_mod

/-- For any positive `k`, `k / 2 < k`. -/
lemma div_two_lt (k : ℕ) (hk : 0 < k) : k / 2 < k :=
  Nat.div_lt_self hk (by decide)

/-- For any `k` with `3 ≤ k`, the division `k / 2` is positive. -/
lemma div_two_pos (k : ℕ) (hk : 3 ≤ k) : 0 < k / 2 :=
  Nat.div_pos (by omega) (by omega)

/-- For any `k` with `k / 2` positive (and hence `k` positive), `k - k / 2 < k`. -/
lemma sub_div_two_lt (k : ℕ) (hk : 0 < k) (hdiv : 0 < k / 2) : k - k / 2 < k :=
  Nat.sub_lt hk hdiv

/--
If `d ∣ b`, then `(a + b) % d = a % d`.
-/
lemma add_mod_eq_of_dvd (a b d : ℕ) (h : d ∣ b) : (a + b) % d = a % d := by
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h, add_zero, Nat.mod_mod]

/--
For `0 < b` and `o ≤ k`, `b^k / b^o = b^(k - o)`.
-/
lemma pow_div_pow_eq_pow_sub (b k o : ℕ) (hb : 0 < b) (ho : o ≤ k) : b ^ k / b ^ o = b ^ (k - o) := by
  have hpos : 0 < b ^ o := Nat.pow_pos hb
  apply Nat.div_eq_of_eq_mul_right hpos
  calc
    b ^ k = b ^ ((k - o) + o) := by rw [Nat.sub_add_cancel ho]
    _ = b ^ (k - o) * b ^ o := by rw [Nat.pow_add]
    _ = b ^ o * b ^ (k - o) := by rw [mul_comm]

/--
`b^(k-o) * b^m = b^((k+m) - o)` when `o ≤ k`.
-/
lemma pow_sub_mul_pow_eq_pow_add_sub (b m k o : ℕ) (ho : o ≤ k) :
    b ^ (k - o) * b ^ m = b ^ ((k + m) - o) := by
  calc
    b ^ (k - o) * b ^ m = b ^ ((k - o) + m) := by rw [Nat.pow_add]
    _ = b ^ ((k + m) - o) := by rw [show (k - o) + m = (k + m) - o by omega]

/--
`(a * b^k) / b^o = a * b^(k-o)` when `0 < b` and `o ≤ k`.
-/
lemma mul_pow_div_pow_eq_mul_pow_sub (a b k o : ℕ) (hb : 0 < b) (ho : o ≤ k) :
    (a * b ^ k) / b ^ o = a * b ^ (k - o) := by
  rw [Nat.mul_div_assoc a (Nat.pow_dvd_pow b ho),
    pow_div_pow_eq_pow_sub b k o hb ho]

/--
`(a / b^o) * b^k + (a % b^o) * b^(k-o) = a * b^(k-o)` when `o ≤ k`.
-/
lemma div_mul_pow_add_mod_mul_pow_sub (a b o k : ℕ) (ho : o ≤ k) :
    (a / b ^ o) * b ^ k + (a % b ^ o) * b ^ (k - o) = a * b ^ (k - o) := by
  calc
    (a / b ^ o) * b ^ k + (a % b ^ o) * b ^ (k - o)
        = (a / b ^ o) * (b ^ o * b ^ (k - o)) + (a % b ^ o) * b ^ (k - o) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' ho]
    _ = ((a / b ^ o) * b ^ o) * b ^ (k - o) + (a % b ^ o) * b ^ (k - o) := by rw [mul_assoc]
    _ = ((a / b ^ o) * b ^ o + a % b ^ o) * b ^ (k - o) := by rw [← add_mul]
    _ = ((b ^ o) * (a / b ^ o) + a % b ^ o) * b ^ (k - o) := by
      rw [mul_comm (a / b ^ o) (b ^ o)]
    _ = a * b ^ (k - o) := by rw [Nat.div_add_mod a (b ^ o)]

/--
If `a + b ≤ n`, then `a ≤ n`.
-/
lemma le_of_add_le_left (a b n : ℕ) (h : a + b ≤ n) : a ≤ n := by
  have : a ≤ a + b := Nat.le_add_right a b
  exact Nat.le_trans this h

/--
If `a + b ≤ n`, then `b ≤ n`.
-/
lemma le_of_add_le_right (a b n : ℕ) (h : a + b ≤ n) : b ≤ n := by
  have : b ≤ a + b := Nat.le_add_left b a
  exact Nat.le_trans this h

end Nat
