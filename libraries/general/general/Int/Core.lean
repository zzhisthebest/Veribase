import Mathlib

namespace Int


/-! ### Absolute difference (as `Nat`) -/

/-- Absolute difference between two `Int` values, as a `Nat`.
`absDiff a b = |a - b|` computed via `Int.natAbs`. -/
def absDiff (a b : Int) : Nat :=
  Int.natAbs (a - b)


lemma absDiff_nonneg (a b : Int) : 0 ≤ absDiff a b := by
  unfold absDiff; exact Nat.zero_le _


lemma absDiff_self (a : Int) : absDiff a a = 0 := by
  simp [absDiff]

lemma absDiff_comm (a b : Int) : absDiff a b = absDiff b a := by
  rw [absDiff, absDiff, ← Int.natAbs_neg (a - b), neg_sub]


/-! ### Closed interval length -/

/-- Length of the closed integer interval `[l, r]` as a natural number.
When `l ≤ r`, this is `r - l + 1`. When `l > r`, returns `1` since
`(r - l).toNat` clips negative values to `0`. -/
def intervalLength (l r : Int) : Nat :=
  ((r - l).toNat) + 1


/-! ### Nonnegative modulo -/

/-- Normalize an integer `n` modulo `m` to the range `[0, m)`.
This is `((n % m) + m) % m`, which always returns a nonnegative result
regardless of the sign of `n`. -/
def nonnegMod (n m : Int) : Int := ((n % m) + m) % m

lemma nonnegMod_nonneg {n m : Int} (hm : 0 < m) : 0 ≤ nonnegMod n m := by
  dsimp [nonnegMod]
  have hm_ne : m ≠ 0 := by omega
  exact Int.emod_nonneg _ hm_ne

lemma nonnegMod_lt {n m : Int} (hm : 0 < m) : nonnegMod n m < m := by
  dsimp [nonnegMod]
  exact Int.emod_lt_of_pos _ hm


/-! ### Ceiling division -/

/-- Ceiling division: `⌈a / b⌉` computed via the floor-through-ceiling identity
`-(Int.ediv (-a) b)`. When `b > 0`, this is the smallest integer `q` such that
`a ≤ q * b`. For `b = 0`, the result is `0` (by mathlib's convention that
`ediv` with divisor `0` returns `0`). -/
def ceilDiv (a b : Int) : Int := - (Int.ediv (-a) b)


end Int

namespace Int

/-! ### Temperature conversion

Uses integer (truncating) division, rounding toward zero. For precise results,
use rational or floating-point arithmetic. -/

/-- Integer-based Celsius to Fahrenheit conversion: `F = C * 9 / 5 + 32`.
Uses truncating division (rounds toward zero). Example:
`celsiusToFahrenheit (-40) = (-40 * 9) / 5 + 32 = -40`. -/
def celsiusToFahrenheit (c : Int) : Int :=
  (c * 9) / 5 + 32

end Int


namespace Int


/-! ### 32-bit signed integer range constants -/

/-- Minimum value of a 32-bit signed integer: `-(2^31)`. -/
def int32Min : Int := -(2 ^ 31)

/-- Maximum value of a 32-bit signed integer: `2^31 - 1`. -/
def int32Max : Int := (2 ^ 31) - 1


lemma int32Min_lt_int32Max : int32Min < int32Max := by
  unfold int32Min int32Max
  omega


lemma int32Min_nonpos : int32Min ≤ 0 := by
  unfold int32Min; omega


lemma int32Max_nonneg : 0 ≤ int32Max := by
  unfold int32Max; omega



/-! ### `natAbs` equals `toNat` for nonnegative integers -/

/-- For a nonnegative integer `s`, `natAbs s = s.toNat`. -/
lemma natAbs_eq_toNat_of_nonneg {s : Int} (hs : s ≥ 0) : Int.natAbs s = s.toNat := by
  have h1 := Int.natAbs_of_nonneg hs
  have h2 := Int.toNat_of_nonneg hs
  have h3 : (Int.natAbs s : Int) = (s.toNat : Int) := by rw [h1, h2]
  exact_mod_cast h3

/-- For a negative integer `s`, `natAbs s = (-s).toNat`. -/
lemma natAbs_eq_toNat_neg_of_neg {s : Int} (hs : s < 0) : Int.natAbs s = (-s).toNat := by
  have h_nonneg : 0 ≤ -s := by omega
  have h := natAbs_eq_toNat_of_nonneg h_nonneg
  rw [Int.natAbs_neg s] at h
  exact h

/-- If `a ≤ s ≤ b`, then `natAbs s ≤ max (natAbs a) (natAbs b)`. -/
lemma natAbs_le_max_natAbs {a s b : Int} (ha : a ≤ s) (hb : s ≤ b) :
    Int.natAbs s ≤ Nat.max (Int.natAbs a) (Int.natAbs b) := by
  by_cases hs_nonneg : s ≥ 0
  · have hb_nonneg : b ≥ 0 := by omega
    rw [natAbs_eq_toNat_of_nonneg hs_nonneg, natAbs_eq_toNat_of_nonneg hb_nonneg]
    have h_toNat : s.toNat ≤ b.toNat := Int.toNat_le_toNat hb
    exact le_trans h_toNat (Nat.le_max_right _ _)
  · have hs_neg : s < 0 := by omega
    have ha_neg : a < 0 := by omega
    rw [natAbs_eq_toNat_neg_of_neg hs_neg, natAbs_eq_toNat_neg_of_neg ha_neg]
    have h_neg : -s ≤ -a := by omega
    have h_toNat : (-s).toNat ≤ (-a).toNat := Int.toNat_le_toNat h_neg
    exact le_trans h_toNat (Nat.le_max_left _ _)

/-- For a negative integer `n`, `(natAbs n : ℤ) = -n`. This is the dual of
`Int.natAbs_of_nonneg`. -/
lemma natAbs_of_neg {n : Int} (hn : n < 0) : (natAbs n : Int) = -n := by
  have h_nonneg_neg : 0 ≤ -n := by omega
  calc
    (natAbs n : Int) = (natAbs (-n) : Int) := by simp
    _ = -n := by simpa using Int.natAbs_of_nonneg h_nonneg_neg

/-- If `a, b ∈ [m, M]` are both bounded by `m` and `M`, then the absolute difference
`|a - b|` is bounded by the range width `|M - m|`. In other words, the maximum possible
`natAbs` difference between any two elements in `[m, M]` is `|M - m|`. -/
lemma natAbs_sub_le_of_bound {a b M m : Int} (ha_le : a ≤ M) (ha_ge : m ≤ a) (hb_le : b ≤ M) (hb_ge : m ≤ b) :
    Int.natAbs (a - b) ≤ Int.natAbs (M - m) := by
  have h_nonneg : 0 ≤ M - m := by omega
  by_cases hge : a ≥ b
  · -- case a ≥ b, then a - b ≥ 0
    have h_nonneg_diff : 0 ≤ a - b := by omega
    have h_upper : a - b ≤ M - m := by omega
    have h_cast1 : (Int.natAbs (a - b) : ℤ) = a - b := Int.natAbs_of_nonneg h_nonneg_diff
    have h_cast2 : (Int.natAbs (M - m) : ℤ) = M - m := Int.natAbs_of_nonneg h_nonneg
    have h_ineq_ℤ : (Int.natAbs (a - b) : ℤ) ≤ (Int.natAbs (M - m) : ℤ) := by
      rw [h_cast1, h_cast2]
      exact h_upper
    exact (Nat.cast_le (α := ℤ)).mp h_ineq_ℤ
  · -- case a < b, then b - a > 0
    have h_lt : a < b := by omega
    have h_nonneg_diff : 0 ≤ b - a := by omega
    have h_upper : b - a ≤ M - m := by omega
    have h_diff_eq : Int.natAbs (a - b) = Int.natAbs (b - a) := by
      have : a - b = -(b - a) := by omega
      rw [this, Int.natAbs_neg]
    rw [h_diff_eq]
    have h_cast1 : (Int.natAbs (b - a) : ℤ) = b - a := Int.natAbs_of_nonneg h_nonneg_diff
    have h_cast2 : (Int.natAbs (M - m) : ℤ) = M - m := Int.natAbs_of_nonneg h_nonneg
    have h_ineq_ℤ : (Int.natAbs (b - a) : ℤ) ≤ (Int.natAbs (M - m) : ℤ) := by
      rw [h_cast1, h_cast2]
      exact h_upper
    exact (Nat.cast_le (α := ℤ)).mp h_ineq_ℤ

/-! ### Natural numbers cannot be negative as integers -/

/-- A natural number cast to `ℤ` is never equal to any negative integer `.negSucc n`. -/
lemma natCast_ne_negSucc {k n : ℕ} : (k : Int) ≠ .negSucc n := by
  intro h_eq
  have h_nonneg : (0 : Int) ≤ (k : Int) := Nat.cast_nonneg _
  rw [h_eq] at h_nonneg
  have h_neg : (.negSucc n : Int) < 0 := by omega
  linarith

/-- A natural number cast to `ℤ` is never equal to `-1`.
This is a specialization of `natCast_ne_negSucc`, provided as a convenience
since `-1` is a common sentinel value. -/
lemma natCast_ne_neg_one {n : ℕ} : (n : Int) ≠ -1 :=
  natCast_ne_negSucc (n := 0)



/-! ### `toNat` distributes over `^` for nonnegative bases -/

/-- For a nonnegative integer `a`, taking `toNat` distributes over exponentiation:
`Int.toNat (a ^ x) = (Int.toNat a) ^ x`. -/
lemma toNat_pow_of_nonneg {a : ℤ} (ha : 0 ≤ a) (x : ℕ) : Int.toNat (a ^ x) = (Int.toNat a) ^ x := by
  rcases Int.eq_ofNat_of_zero_le ha with ⟨n, hn⟩
  subst hn
  rw [← Nat.cast_pow n x, Int.toNat_natCast, Int.toNat_natCast]



/-! ### `toNat` equality bridge -/

/-- For a nonnegative integer `n`, `Int.toNat n = m` (as `ℕ`) iff `n = (m : ℤ)`.
This bridges the natural-number and integer representations. -/
lemma toNat_eq_iff_natCast {n : ℤ} {m : ℕ} (hn : 0 ≤ n) : Int.toNat n = m ↔ n = (m : ℤ) := by
  constructor
  · intro h
    calc
      n = (Int.toNat n : ℤ) := (Int.toNat_of_nonneg hn).symm
      _ = (m : ℤ) := by simp [h]
  · intro h
    have := congrArg Int.toNat h
    simpa using this



/-! ### `toNat` inequality -/

/-- If `0 ≤ a` and `a < (b : ℤ)`, then `a.toNat < b` (in `ℕ`). -/
lemma toNat_lt_of_nonneg_lt {a : Int} {b : Nat} (ha_nonneg : 0 ≤ a) (hab : a < (b : Int)) :
    a.toNat < b := by
  have h : (a.toNat : Int) < (b : Int) := by
    calc
      (a.toNat : Int) = a := Int.toNat_of_nonneg ha_nonneg
      _ < (b : Int) := hab
  exact (Nat.cast_lt (α := Int)).mp h

/-- A positive integer converts to a nonzero natural number. -/
lemma toNat_ne_zero_of_pos {n : Int} (h : n > 0) : n.toNat ≠ 0 := by omega

/-- The `Int.toNat` of the negation of a negative integer is nonzero.
This is the dual of `toNat_ne_zero_of_pos` for the negative case: when `n < 0`,
`(-n).toNat ≠ 0` because `-n` is positive. -/
lemma toNat_neg_ne_zero_of_lt {n : Int} (hn : n < 0) : (-n).toNat ≠ 0 := by
  have hpos : 0 < -n := by linarith
  exact toNat_ne_zero_of_pos hpos

/-- If `n : ℤ` satisfies `n ≤ (m : ℤ)` for `m : ℕ`, then `n.toNat ≤ m`. -/
lemma toNat_le_of_le_nat {n : ℤ} {m : ℕ} (h : n ≤ (m : ℤ)) : n.toNat ≤ m := by
  have h_le := Int.toNat_le_toNat h
  simpa using h_le

/-- If an integer `n` is not nonpositive, then `1 ≤ n.toNat`. -/
lemma one_le_toNat_of_not_nonpos {n : ℤ} (h : ¬ n ≤ 0) : 1 ≤ n.toNat := by
  have h_one_int : (1 : ℤ) ≤ n := by omega
  have h_le := Int.toNat_le_toNat h_one_int
  simpa using h_le

/-- For any integer `n`, `n > 1` is equivalent to `2 ≤ n.toNat` (in `ℕ`).
This bridges `Int` and `Nat` inequality reasoning, and holds for negative `n`
since both sides are false for `n ≤ 1`. -/
lemma gt_one_iff_two_le_toNat (n : Int) : (n > 1) ↔ (2 ≤ n.toNat) := by
  omega

/-- For `n : Int` and `k : ℕ` with `k > 0`, `n.toNat ≥ k` is equivalent to `n ≥ (k : Int)`.
This bridges `Nat` and `Int` inequality reasoning. The `k > 0` hypothesis is needed:
when `k = 0`, the left side is always true but the right side fails for negative `n`. -/
lemma toNat_ge_iff (n : Int) {k : ℕ} (hk : 0 < k) : n.toNat ≥ k ↔ n ≥ (k : Int) := by
  constructor
  · intro h
    have h_nonneg : n ≥ 0 := by
      by_contra hneg
      have : n.toNat = 0 := Int.toNat_of_nonpos (by omega)
      omega
    have h_eq : (n.toNat : Int) = n := Int.toNat_of_nonneg h_nonneg
    omega
  · intro h
    have h_nonneg : n ≥ 0 := by omega
    have h_eq : (n.toNat : Int) = n := Int.toNat_of_nonneg h_nonneg
    omega

/-- `Nat.Prime n.toNat` is equivalent to `n > 1` and the usual divisor condition
in `ℕ`. This is a specialization of `Nat.prime_def` for `Int.toNat`, replacing
`2 ≤ n.toNat` with the more convenient `n > 1`. -/
lemma natPrime_toNat_iff (n : Int) : (Nat.Prime n.toNat) ↔ (n > 1 ∧ ∀ m : Nat, m ∣ n.toNat → m = 1 ∨ m = n.toNat) := by
  rw [Nat.prime_def, gt_one_iff_two_le_toNat n]


end Int

namespace Int


/-! ### Trichotomy lemmas -/

/-- If an integer is neither positive nor negative, then it must be zero.
This is a convenient form of trichotomy: `¬ n > 0 ∧ ¬ n < 0 → n = 0`. -/
lemma not_pos_not_neg_eq_zero {n : Int} (hpos : ¬ n > 0) (hneg : ¬ n < 0) : n = 0 := by
  omega



/-! ### Basic sign lemmas -/

/-- A positive integer is not negative: `a > 0` implies `¬ a < 0`. -/
lemma not_lt_zero_of_pos {a : Int} (h : a > 0) : ¬ a < 0 := by omega

/-- If an integer is not less than zero, then it is greater than or equal to zero.
This is `le_of_not_gt` specialized to `0` for convenience. -/
lemma ge_zero_of_not_lt_zero {n : Int} (h : ¬ n < 0) : n ≥ 0 := by omega

/-- A positive integer is nonzero. -/
lemma ne_zero_of_pos {a : Int} (h : a > 0) : a ≠ 0 := by omega

/-- A negative integer is nonzero. -/
lemma ne_zero_of_neg {a : Int} (h : a < 0) : a ≠ 0 := by omega



/-! ### Sign-based classification

`classifyByScore s` maps an integer to a label based on its sign:
`"positive"` when `s > 0`, `"negative"` when `s < 0`, and `"neutral"` when `s = 0`.
This is a specialization of `compareLabel` (in `general.Order`) with fixed string labels
for sentiment-analysis and similar sign-classification patterns.

The lemma `classifyByScore_spec` captures the full specification: the label is one of
the three strings, and the label is correctly correlated with the sign. -/

/-- Classify an integer score into a sentiment label based on its sign.
Returns `"positive"` if `s > 0`, `"negative"` if `s < 0`, and `"neutral"` if `s = 0`.
Equivalent to `compareLabel s 0 "positive" "negative" "neutral"`. -/
def classifyByScore (s : Int) : String :=
  if s > 0 then "positive"
  else if s < 0 then "negative"
  else "neutral"

/-- Full specification of `classifyByScore`: the result is always one of the three valid
labels, and each label correctly tracks the sign of the input integer. -/
lemma classifyByScore_spec (s : Int) :
    (classifyByScore s = "positive" ∨ classifyByScore s = "negative" ∨ classifyByScore s = "neutral") ∧
    ((classifyByScore s = "positive" ∧ s > 0) ∨
     (classifyByScore s = "negative" ∧ s < 0) ∨
     (classifyByScore s = "neutral" ∧ s = 0)) := by
  unfold classifyByScore
  by_cases hpos : s > 0
  · simp [hpos]
  · by_cases hneg : s < 0
    · simp [hpos, hneg]
    · have hzero : s = 0 := by omega
      simp [hpos, hneg, hzero]


end Int

namespace Int

/-! ### Squared Euclidean distance in 2D -/

/-- Squared Euclidean distance in the integer plane:
`dist2 (x₁, y₁) (x₂, y₂) = (x₁ - x₂)² + (y₁ - y₂)²`.
This avoids floating-point and square roots, making it ideal for
exact integer computations in geometry problems. -/
def dist2 (a b : Int × Int) : Int :=
  let (x1, y1) := a
  let (x2, y2) := b
  (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)

/-! ### Manhattan (L1) distance in 2D -/

/-- Manhattan (L1) distance between two integer-coordinate points:
`manhattanDist (x₁, y₁) (x₂, y₂) = |x₁ - x₂| + |y₁ - y₂|`. -/
def manhattanDist (p q : Int × Int) : Nat :=
  Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2)


lemma manhattanDist_nonneg (p q : Int × Int) : 0 ≤ manhattanDist p q := by
  unfold manhattanDist; exact Nat.zero_le _

end Int
