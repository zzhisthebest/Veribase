import Mathlib
import vericontest.Nat

namespace Int

/-- Recursively computes `2^e` for an integer exponent `e`.
For `e ≤ 0`, returns `1`. For `e > 0`, returns `2 * pow2_int (e - 1)`.
This is a simple integer power function specialized to base 2,
useful when mathlib's `(2 : ℤ) ^ e` is inconvenient to unfold. -/
def pow2_int (e : Int) : Int :=
  if e ≤ 0 then 1 else 2 * pow2_int (e - 1)
termination_by e.toNat

lemma pow2_int_eq_one_of_nonpos (e : Int) (h : e ≤ 0) : pow2_int e = 1 := by
  unfold pow2_int; simp [h]

lemma pow2_int_succ_of_nonneg (e : Int) (h : 0 ≤ e) : pow2_int (e + 1) = 2 * pow2_int e := by
  have hpos : ¬ (e + 1 ≤ 0) := by omega
  conv =>
    lhs
    unfold pow2_int
  rw [if_neg hpos]
  congr
  omega

lemma pow2_int_pos (e : Int) : 0 < pow2_int e := by
  by_cases h : e ≤ 0
  · rw [pow2_int_eq_one_of_nonpos e h]; omega
  · have h_nonneg : 0 ≤ e := by omega
    refine (Int.le_induction (P := λ x => 0 < pow2_int x) ?h0 ?hstep e h_nonneg)
    · have : pow2_int (0 : Int) = 1 := pow2_int_eq_one_of_nonpos 0 (by omega)
      simp [this]
    · intro n hn hpos
      rw [pow2_int_succ_of_nonneg n hn]
      nlinarith

lemma pow2_int_nonneg (e : Int) : 0 ≤ pow2_int e := by
  have hpos := pow2_int_pos e; omega

lemma pow2_int_of_pos (n : Int) (hn : 0 < n) : pow2_int n = 2 * pow2_int (n - 1) := by
  have hn' : 0 ≤ n - 1 := by omega
  simpa [sub_add_cancel] using pow2_int_succ_of_nonneg (n - 1) hn'

/-- `Int.even` is the `Bool`-valued parity predicate: `even n` is true iff `n` is even.
This is the `Bool` counterpart to the `Even` `Prop` predicate; useful with `decide`
and in computational contexts (e.g., competitive programming solutions). -/
def even (value : Int) : Bool :=
  value % 2 = 0

/-- `Int.odd` is the `Bool`-valued oddness predicate: `odd n` is true iff `n` is odd.
This is the `Bool` counterpart to `¬ Int.even n`; useful with `decide`
and in computational contexts (e.g., checking for three consecutive odd numbers). -/
def odd (value : Int) : Bool :=
  value % 2 = 1

/-- Ceiling of `x / 2` for integers: `⌈x/2⌉ = (x + 1) / 2`.
This uses the identity `⌈x/2⌉ = ⌊(x+1)/2⌋` which holds for all integers
because integer division in Lean truncates toward negative infinity. -/
def ceilHalf (x : ℤ) : ℤ := (x + 1) / 2

/-- Ceiling integer division: `⌈a / b⌉`. For `b > 0`, this equals `(a + b - 1) / b`,
which is the standard identity for ceiling division when integer division truncates
toward negative infinity (as `Int.ediv` does). For `b ≤ 0`, returns `0` as a safe default.
This generalizes `ceilHalf` to arbitrary positive denominators. -/
def ceilDiv_specificDuplicate (a b : Int) : Int :=
  if b > 0 then (a + b - 1) / b else 0

/-- Ceiling division bounds: for `b > 0`, `(ceilDiv_specificDuplicate a b - 1) * b < a` and
`a ≤ (ceilDiv_specificDuplicate a b) * b`. This is the fundamental property of ceiling division:
the ceiling times the denominator is at least the numerator, but subtracting 1
from the ceiling makes it strictly less. -/
lemma ceilDiv_prop {a b : ℤ} (hb : 0 < b) :
    (ceilDiv_specificDuplicate a b - 1) * b < a ∧ a ≤ (ceilDiv_specificDuplicate a b) * b := by
  have hbpos : b > 0 := hb
  simp [ceilDiv_specificDuplicate, hbpos]
  set q := (a + b - 1) / b
  have hb_ne_zero : b ≠ 0 := by omega
  have hlower : q * b ≤ a + b - 1 := Int.ediv_mul_le (a + b - 1) hb_ne_zero
  have hupper : a + b - 1 < (q + 1) * b := Int.lt_ediv_add_one_mul_self (a + b - 1) hb
  have h1 : (q - 1) * b < a := by
    have : (q - 1) * b = q * b - b := by ring
    rw [this]
    omega
  have h2 : a ≤ q * b := by
    have : (q + 1) * b = q * b + b := by ring
    rw [this] at hupper
    omega
  exact And.intro h1 h2

/-- Monotonicity of `ceilDiv_specificDuplicate` in the numerator: if `a ≤ a'` and `b > 0`, then
`ceilDiv_specificDuplicate a b ≤ ceilDiv_specificDuplicate a' b`. -/
lemma ceilDiv_mono {a a' b : ℤ} (ha : a ≤ a') (hb : 0 < b) : ceilDiv_specificDuplicate a b ≤ ceilDiv_specificDuplicate a' b := by
  have hbpos : b > 0 := hb
  simp [ceilDiv_specificDuplicate, hbpos]
  have h : a + b - 1 ≤ a' + b - 1 := by omega
  exact Int.ediv_le_ediv hb h

/-- If `1 ≤ x ≤ d`, then `ceilDiv_specificDuplicate x d = 1`. This captures the property that
when the numerator is positive and bounded by the denominator, ceiling division
gives exactly 1. Useful in problems where values are capped at the divisor
(e.g., Koko eats at most one hour per pile at maximum speed). -/
lemma ceilDiv_eq_one_of_pos_of_le {x d : ℤ} (hx : 1 ≤ x) (hxd : x ≤ d) : ceilDiv_specificDuplicate x d = 1 := by
  have hd : 0 < d := lt_of_lt_of_le (by omega) hxd
  unfold ceilDiv_specificDuplicate
  simp [hd]
  have hqlo : 1 ≤ (x + d - 1) / d := by
    rw [Int.le_ediv_iff_mul_le hd]
    omega
  have hqhi : ¬ 2 ≤ (x + d - 1) / d := by
    intro hq
    have hh := (Int.le_ediv_iff_mul_le hd).mp hq
    omega
  omega

/-- For any integer `k`, `(k+1)/2 + k/2 = k`. This is the identity that
the ceiling of `k/2` plus the floor of `k/2` equals `k`. -/
lemma ediv_succ_two_add_ediv_two_eq_self (k : Int) : (k + 1) / 2 + k / 2 = k := by
  omega

/-- If `a % b = 0`, then `(a / b) * b = a`. This follows from the fundamental
identity `Int.ediv_add_emod a b` which states `a / b * b + a % b = a`.
When the remainder is zero, the division-exactness condition simplifies to
the multiplication identity. Holds for all `b` (including `b = 0`, where
`a / 0 = 0` and `a % 0 = a`, so the hypothesis forces `a = 0`). -/
lemma ediv_mul_eq_of_mod_eq_zero {a b : ℤ} (h : a % b = 0) : a / b * b = a := by
  have hdiv := Int.ediv_add_emod a b
  rw [h, add_zero] at hdiv
  simpa [mul_comm] using hdiv

/-! ### Prime modulus (10^9 + 7)

The prime `1_000_000_007` is the standard modulus used in competitive programming
and combinatorial modular arithmetic. It is a large prime that fits comfortably
within a 32-bit signed integer, allowing modular computations without overflow
in most languages. -/

/-- The standard competitive programming prime modulus `10^9 + 7 = 1_000_000_007`.
This prime is large enough to minimize collision probability in hashing schemes
and small enough that `(MOD-1)^2` fits in a 64-bit integer (avoiding overflow in
intermediate multiplications). -/
def primeModulus : Int := 1_000_000_007

/-! ### Modular arithmetic lemmas -/

/-- When computing `(a * b) % m`, any factor can be taken modulo `m` first while
preserving the result. Specifically, `((a % m) * b) % m = (a * b) % m`.
This follows from `Int.mul_emod` and `Int.emod_emod`. -/
lemma mod_mul_mod_eq_mul_mod (a b m : ℤ) : ((a % m) * b) % m = (a * b) % m := by
  calc
    ((a % m) * b) % m = (((a % m) % m) * (b % m)) % m := by rw [Int.mul_emod]
    _ = ((a % m) * (b % m)) % m := by rw [Int.emod_emod]
    _ = (a * b) % m := by rw [← Int.mul_emod]

/-- A modular sum variant: `((a % m) * b + c) % m = (a * b + c) % m`.
Useful for simplifying modulo computations involving sums of products.
Depends on `mod_mul_mod_eq_mul_mod`. -/
lemma mod_mul_add_mod_eq_mul_add_mod (a b c m : ℤ) : ((a % m) * b + c) % m = (a * b + c) % m := by
  calc
    ((a % m) * b + c) % m = (((a % m) * b) % m + c % m) % m := by rw [Int.add_emod]
    _ = ((a * b) % m + c % m) % m := by rw [mod_mul_mod_eq_mul_mod]
    _ = (a * b + c) % m := by rw [← Int.add_emod]

/-- `(k * m) % b` for integers. The last digit of `k*m` in base `b` arithmetic.
For `b = 10` this gives the standard decimal last digit of the product. -/
def lastDigitBase (b k m : Int) : Int := (k * m) % b

/-- Sum of `lastDigitBase b (k+1) m` for `k` in `range b.natAbs`.
Requires `b > 0` for the cycle property to make sense. -/
def lastDigitCycleSum (b m : Int) : Int :=
  (Finset.range b.natAbs).sum fun k => lastDigitBase b ((k : Int) + 1) m

/-- Prefix sum of the last-digit sequence: sum of `lastDigitBase b i m` for `i = 1` to `rem`.
Defined recursively with termination on `rem.toNat`. -/
def lastDigitPrefixSum (rem m : Int) (b : Int := 10) : Int :=
  if rem ≤ 0 then
    0
  else
    lastDigitPrefixSum (rem - 1) m b + lastDigitBase b rem m
termination_by rem.toNat

/-- Efficient computation of ∑_{k=1}^{t} ((k * m) % b), using the period `b` of
`lastDigitBase b k m`. The sum is decomposed into full cycles plus a prefix remainder. -/
def sumLastDigitsBase (b t m : Int) : Int :=
  (t / b) * lastDigitCycleSum b m + lastDigitPrefixSum (t % b) m b

lemma lastDigitBase_eq_natCast (k m : Nat) :
    ((Nat.lastDigitBase 10 k m : Nat) : Int) = lastDigitBase (10 : Int) (k : Int) (m : Int) := by
  unfold Nat.lastDigitBase lastDigitBase
  simp

lemma lastDigitCycleSum_eq_natCast (m : Nat) :
    ((Nat.lastDigitCycleSum 10 m : Nat) : Int) = lastDigitCycleSum (10 : Int) (m : Int) := by
  unfold Nat.lastDigitCycleSum lastDigitCycleSum
  simp [lastDigitBase_eq_natCast]

lemma lastDigitPrefixSum_eq_natCast (rem m : Nat) :
    ((Nat.lastDigitPrefixSum 10 rem m : Nat) : Int) = lastDigitPrefixSum (rem : Int) (m : Int) 10 := by
  induction' rem with rem' ih
  · simp [Nat.lastDigitPrefixSum, lastDigitPrefixSum]
  · rw [Nat.lastDigitPrefixSum_succ 10 rem' m, Nat.cast_add, ih, lastDigitBase_eq_natCast,
      show ((rem' + 1 : Nat) : Int) = (rem' : Int) + 1 by simp]
    have h_not_le : ¬ ((rem' : Int) + 1 ≤ 0) := by
      have hnn : (0 : Int) ≤ (rem' : Int) := Nat.cast_nonneg _
      omega
    have h_sub : ((rem' : Int) + 1) - 1 = (rem' : Int) := by omega
    -- Rewrite LHS: replace (rem':Int) with ((rem':Int)+1)-1
    rw [← h_sub]
    -- Goal: lastDigitPrefixSum (((rem' : Int) + 1) - 1) (m : Int) 10 + ... = lastDigitPrefixSum ((rem' : Int) + 1) (m : Int) 10
    -- Unfold the RHS only, then simplify the if-condition
    conv =>
      rhs
      unfold lastDigitPrefixSum
    simp [h_not_le]

lemma sumLastDigitsBase_eq_natCast (t m : Nat) :
    ((Nat.sumLastDigitsBase 10 t m : Nat) : Int) = sumLastDigitsBase (10 : Int) (t : Int) (m : Int) := by
  unfold Nat.sumLastDigitsBase sumLastDigitsBase
  simp [lastDigitCycleSum_eq_natCast, lastDigitPrefixSum_eq_natCast]

/-- If `x : ℤ` satisfies `1 ≤ x` and `x ≤ (n : ℤ)` for a `Nat` `n`,
then `(x - 1).toNat < n`. This is useful for converting integer index ranges
back to natural number bounds. -/
lemma toNat_sub_one_lt_of_one_le_of_le_nat {x : Int} {n : Nat}
    (hx_pos : 1 ≤ x) (hx_le : x ≤ (n : Int)) :
    (x - 1).toNat < n := by
  omega

/-! ### One-based index arithmetic -/

/-- Any natural index is positive when converted to a one-based integer index:
`idx` in ℕ gives `(idx : ℤ) + 1 ≥ 1`. -/
lemma oneBasedIndex_pos (idx : Nat) : 1 ≤ (idx : Int) + 1 := by
  omega

/-- If `idx < upper` in ℕ, then in one-based ℤ indexing `idx+1 ≤ upper`.
Useful for bounding one-based index results by the list length. -/
lemma oneBasedIndex_le_of_lt {idx upper : Nat} (hlt : idx < upper) :
    (idx : Int) + 1 ≤ (upper : Int) := by
  have hle : idx + 1 ≤ upper := Nat.succ_le_of_lt hlt
  exact_mod_cast hle

/-- One-based modular position: given a position `x` (1-indexed) and modulus `n`,
returns `(x-1) % n + 1`. This converts to 0-based, takes the remainder,
then converts back to 1-based. Useful for wrapping positions in grid layouts. -/
def oneBasedMod (x n : Int) : Int :=
  (x - 1) % n + 1

/-- If `1 ≤ n` for a natural `n`, then `((n - 1 : ℕ) : α) = (n : α) - 1`
for any `AddGroupWithOne α`. This is a convenient special case of `Nat.cast_sub`
with the second argument fixed to `1`. -/
lemma nat_cast_sub_one {α : Type} [AddGroupWithOne α] {n : ℕ} (h : 1 ≤ n) : ((n - 1 : ℕ) : α) = (n : α) - 1 := by
  simpa using Nat.cast_sub h

/-! ### max4 — maximum of four values -/

/-- The maximum of four values: `max4 a b c d = max (max a b) (max c d)`.
This is equivalent to `[a, b, c, d].maximum` but is often more convenient to unfold
in proofs about multi-variable maxima (e.g., finding the maximum of four symmetric
cells in a matrix). -/
def max4 {α : Type _} [LinearOrder α] (a b c d : α) : α := max (max a b) (max c d)

/-! ### `toNat` lemmas -/

/-- If `value : ℤ` equals a natural number `n` (as `(n : ℤ)`), then `value.toNat = n`.
This wraps `Int.toNat_ofNat` into a single rewrite step, useful when the equality
comes from a hypothesis rather than being discovered by `simp`. -/
lemma toNat_eq_of_eq_natCast {value : ℤ} {n : ℕ} (h : value = n) : value.toNat = n := by
  rw [h]
  exact Int.toNat_ofNat n

/-- `Int.toNat (n : ℤ) = n` for any natural number `n`.
This is a direct `simp` lemma that bridges `Int.toNat` and `Nat.cast`. -/
lemma toNat_natCast_eq (n : ℕ) : Int.toNat (n : ℤ) = n := by
  simp

/-- For `a b : ℕ`, `((a : ℤ) * (b : ℤ)).toNat = a * b`.
This holds because the product of two nonnegative integers is nonnegative,
so `Int.toNat` acts as the identity on the product. Useful when converting
between `ℤ`-based and `ℕ`-based arithmetic in competitive programming specs. -/
lemma toNat_mul_natCast (a b : ℕ) : ((a : ℤ) * (b : ℤ)).toNat = a * b := by
  omega

/-- If `x : ℤ` is bounded above by `(n : ℤ)` (where `n : ℕ`), then `x.toNat ≤ n`.
This works even when `x` is negative (`x.toNat = 0 ≤ n`) and follows from
`Int.toNat_le_toNat` plus `toNat_natCast_eq`. -/
lemma toNat_le_nat {x : Int} {n : Nat} (h : x ≤ (n : Int)) : x.toNat ≤ n := by
  have := Int.toNat_le_toNat h
  simpa using this

/-- If `(q : ℤ) < k` for `q : ℕ` and `k : ℤ`, then `q < k.toNat`.
This is the `Nat`-cast companion to `toNat_lt_of_nonneg_lt_specificDuplicate`: it converts a `ℤ` inequality
involving a `Nat` cast to a pure `ℕ` inequality. The nonnegativity of `k` follows from
`(q : ℤ) < k` and `0 ≤ (q : ℤ)`. -/
lemma nat_lt_toNat_of_int_lt {q : Nat} {k : Int} (h : (q : Int) < k) :
    q < k.toNat := by
  have hk : 0 ≤ k := by omega
  have : (q : Int) < (k.toNat : Int) := by
    simpa [Int.toNat_of_nonneg hk] using h
  exact_mod_cast this

/-- If `1 ≤ x : ℤ`, then `1 ≤ x.toNat : ℕ`. Companion to `toNat_le_nat` for the
lower-bound direction, useful when converting positive integer bounds to
natural number minimal indices. -/
lemma one_le_toNat {x : Int} (h : 1 ≤ x) : 1 ≤ x.toNat := by
  have := Int.toNat_le_toNat h
  simpa using this

/-- If `0 ≤ i`, `0 ≤ len`, and `i + len ≤ (n : ℤ)` for a `Nat` `n`, then
`i.toNat + len.toNat ≤ n`. This is the key lemma for converting integer
index-range bounds `i + len ≤ n` to natural-number index arithmetic,
using `Int.toNat_add` to distribute `toNat` over addition. -/
lemma toNat_add_le_nat {i len : Int} {n : Nat} (hi : 0 ≤ i) (hl : 0 ≤ len) (h : i + len ≤ (n : Int)) :
    i.toNat + len.toNat ≤ n := by
  have h' := Int.toNat_le_toNat h
  rw [Int.toNat_add hi hl] at h'
  simpa using h'

/-- If `1 ≤ hi` for an integer `hi`, then `(hi - 1).toNat < hi.toNat`.
This is a strict monotonicity property: applying `Int.toNat` after subtracting 1
produces a smaller natural number. Useful for termination proofs and index bounds. -/
lemma toNat_sub_one_lt {hi : ℤ} (hpos : 1 ≤ hi) : Int.toNat (hi - 1) < Int.toNat hi := by
  have h_nonneg_hi : 0 ≤ hi := by omega
  have h_nonneg_hi_m1 : 0 ≤ hi - 1 := by omega
  have h_eq_hi : (Int.toNat hi : ℤ) = hi := Int.toNat_of_nonneg h_nonneg_hi
  have h_eq_hi_m1 : (Int.toNat (hi - 1) : ℤ) = hi - 1 := Int.toNat_of_nonneg h_nonneg_hi_m1
  have h_lt : (Int.toNat (hi - 1) : ℤ) < (Int.toNat hi : ℤ) := by
    rw [h_eq_hi_m1, h_eq_hi]
    omega
  exact_mod_cast h_lt

/-- If `a : ℤ` is nonnegative and `a < (b : ℤ)` for a `Nat` `b`,
then `a.toNat < b`. Useful for converting integer index bounds to natural number bounds. -/
lemma toNat_lt_of_nonneg_lt_specificDuplicate {a : Int} {b : Nat} (ha : 0 ≤ a) (h : a < (b : Int)) : a.toNat < b := by
  have hcast : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h' : (a.toNat : Int) < (b : Int) := by rw [hcast]; exact h
  exact Nat.cast_lt.mp h'

/-- If `0 ≤ a` and `a < b` in `Int`, then `a.toNat < b.toNat`.
This is the `Int`-version of `toNat_lt_of_nonneg_lt_specificDuplicate`: both arguments are `Int`,
and the comparison is on their `toNat` values. Useful when both bounds are
integer-valued (e.g., list lengths cast to `Int`). -/
lemma toNat_lt_toNat_of_nonneg_lt {a b : Int} (ha : 0 ≤ a) (h : a < b) : a.toNat < b.toNat := by
  have hb : 0 < b := by linarith
  exact (Int.toNat_lt_toNat hb).mpr h

/-- If `x : ℤ` is nonnegative and `x.toNat < n`, then `x` equals the integer cast of the
`Fin n` value `⟨x.toNat, h⟩`. This bridges `Int.toNat_of_nonneg` with `Fin.val` casting,
useful when converting `ℤ`-indexed computations to `Fin`-indexed ones for list/matrix access
via `List.get` or `List.ofFn`. -/
lemma fin_val_toNat_eq {n : ℕ} (x : Int) (h : x.toNat < n) (hx : 0 ≤ x) :
    x = ((⟨x.toNat, h⟩ : Fin n).val : Int) := by
  have hval : ((⟨x.toNat, h⟩ : Fin n).val : Int) = (x.toNat : Int) := by simp
  rw [hval]
  exact (Int.toNat_of_nonneg hx).symm

/-- For a nonnegative integer `k`, `(k + 1).toNat = k.toNat + 1`.
This decomposes `Int.toNat` across a `+1` addition, useful for termination proofs
and index arithmetic. -/
lemma toNat_add_one (k : ℤ) (hk : 0 ≤ k) : (k + 1).toNat = k.toNat + 1 := by
  rw [Int.toNat_add hk (by norm_num : 0 ≤ (1 : ℤ))]
  simp

/-- `((k - 1) + 1).toNat = k.toNat` for any integer `k`.
This simplifies the ring expression `(k - 1) + 1` to `k` before applying `Int.toNat`.
Useful when a recursive function decrements then increments the index. -/
lemma toNat_sub_one_add_one (k : ℤ) : ((k - 1) + 1).toNat = k.toNat := by
  have h : (k - 1) + 1 = k := by omega
  simp [h]

/-- When `1 ≤ k`, the integer interval `[1, k)` corresponds exactly to the natural number
interval `{j : Nat | j ≠ 0 ∧ j < k.toNat}` under `Nat.cast`. Specifically,
`1 ≤ r ∧ r < k` iff there exists a nonzero natural `j < k.toNat` with `(j : ℤ) = r`.

This bridges `Int` range conditions to `Nat` range conditions, useful when
array indexing is done in `Nat` but arithmetic uses `Int` (e.g., remainder-based
pair counting with modulo arithmetic). -/
lemma one_le_and_lt_iff_nat {k r : Int} (hk : 1 ≤ k) :
    (1 ≤ r ∧ r < k) ↔ (∃ j : Nat, j ≠ 0 ∧ j < k.toNat ∧ (j : Int) = r) := by
  have hk_pos : 0 < k := by omega
  have hk_nonneg : 0 ≤ k := by omega
  constructor
  · rintro ⟨hr1, hr2⟩
    have hr_nonneg : 0 ≤ r := by omega
    have h_lt_nat : r.toNat < k.toNat :=
      ((Int.toNat_lt_toNat hk_pos).mpr hr2)
    refine ⟨r.toNat, ?_, h_lt_nat, Int.toNat_of_nonneg hr_nonneg⟩
    · intro hzero
      have h_le : r ≤ 0 := (Int.toNat_eq_zero.mp hzero)
      omega
  · rintro ⟨j, hj_ne_zero, hj_lt, hj_eq⟩
    have hj_pos_int : 0 < (j : Int) := by exact_mod_cast Nat.pos_of_ne_zero hj_ne_zero
    have hj_lt_k_int : (j : Int) < k := by
      calc
        (j : Int) < (k.toNat : Int) := by exact_mod_cast hj_lt
        _ = k := Int.toNat_of_nonneg hk_nonneg
    have h_r_pos : 1 ≤ r := by
      rw [← hj_eq]
      omega
    have h_r_lt_k : r < k := by
      rw [← hj_eq]
      exact hj_lt_k_int
    exact ⟨h_r_pos, h_r_lt_k⟩

/-- For nonnegative `a, b : ℤ`, `(a.toNat : ℤ) * (b.toNat : ℤ) = a * b`.
This connects the `Int.toNat` representation of two nonnegative integers to their
original values in a multiplication context. Useful when converting between `Nat`-based
computations and `ℤ`-based arithmetic (e.g., using `Int.toNat` for array lengths
while doing integer arithmetic). -/
lemma cast_toNat_mul {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a.toNat : ℤ) * (b.toNat : ℤ) = a * b := by
  simp [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]

/-- For `a : ℤ` nonnegative and `b : ℕ`, `(a + (b : ℤ)).toNat = a.toNat + b`.
This decomposes `Int.toNat` across an addition of a nonnegative integer and a natural
number, which is more convenient than `Int.toNat_add` when one argument is a `Nat`. -/
lemma toNat_add_natCast {a : ℤ} {b : ℕ} (ha : 0 ≤ a) : (a + (b : ℤ)).toNat = a.toNat + b := by
  omega

/-- For nonnegative `a, b : ℤ` with `1 ≤ a.toNat` (i.e., `a ≥ 1` as a natural),
`(((a.toNat - 1) * b.toNat : ℕ) : ℤ) = (a - 1) * b`.
This handles the common case of converting a `Nat`-based arithmetic expression
involving `Int.toNat` subtraction and multiplication back to `ℤ` arithmetic.
The `1 ≤ a.toNat` hypothesis ensures the subtraction `a.toNat - 1` is well-behaved
as a natural number. -/
lemma toNat_sub_one_mul_eq_sub_one_mul {a b : ℤ} (ha : 0 ≤ a) (ha_one : 1 ≤ a.toNat) (hb : 0 ≤ b) :
    (((a.toNat - 1) * b.toNat : ℕ) : ℤ) = (a - 1) * b := by
  have ha_eq : (a.toNat : ℤ) = a := mod_cast Int.toNat_of_nonneg ha
  have hb_eq : (b.toNat : ℤ) = b := mod_cast Int.toNat_of_nonneg hb
  have h_cast_sub : ((a.toNat - 1 : ℕ) : ℤ) = (a.toNat : ℤ) - 1 := Nat.cast_sub ha_one
  simp [ha_eq, hb_eq, h_cast_sub]

/-! ### Lifting Nat specifications to Int

`liftNat₂` converts a binary `Nat → Nat → Nat` function into an `Int → Int → Int`
function by applying `Int.toNat` to both arguments and casting the result.
This is a generic combinator for problems whose specification is defined on `Nat`
but whose public entry point takes `Int` inputs (common in LeetCode-style problems). -/

/-- Lift a binary `Nat → Nat → Nat` specification to `Int → Int → Int` by
converting arguments via `Int.toNat` and casting the result.

Example: if `f n m = n + m` (on `Nat`), then `liftNat₂ f a b = (a.toNat + b.toNat : ℤ)`.
This is especially useful when the problem spec operates on natural numbers but
the public API function signature uses `Int` (a common pattern in competitive programming). -/
def liftNat₂ (f : Nat → Nat → Nat) (a b : Int) : Int :=
  (f a.toNat b.toNat : Int)

/-- Unfolding lemma for `liftNat₂`: relates the lifted version to the
direct `Int.toNat`/`Nat.cast` pattern. Useful whenever a proof needs to rewrite the
abstract `liftNat₂` back to the concrete representation. -/
@[simp]
theorem liftNat₂_eq (f : Nat → Nat → Nat) (a b : Int) :
    liftNat₂ f a b = (f a.toNat b.toNat : Int) := rfl

/-- Lift a `Nat`-valued function `f : α → Nat` to `Int` via `Nat.cast`.
The unary version of `liftNat₂`. Captures the common pattern where a spec
computes a natural number but the interface requires `Int`. -/
def liftNat {α : Sort u} (f : α → Nat) (x : α) : Int := (f x : Int)

/-- Unfolding lemma for `liftNat`: `liftNat f x = (f x : ℤ)`. -/
@[simp]
theorem liftNat_eq {α : Sort u} (f : α → Nat) (x : α) :
    liftNat f x = (f x : Int) := rfl

/-! ### Integer square root bounds

These lemmas lift the corresponding `Nat.sqrt` bounds (`Nat.sqrt_le` and `Nat.lt_succ_sqrt`)
to `Int.sqrt`. -/

/-- For a nonnegative integer `k`, `Int.sqrt k * Int.sqrt k ≤ k`.
This is the fundamental floor-sqrt upper bound: the integer square root squared
never exceeds the original number. -/
lemma sqrt_mul_self_le (k : Int) (hk : 0 ≤ k) : Int.sqrt k * Int.sqrt k ≤ k := by
  have h_nat : Nat.sqrt (Int.toNat k) * Nat.sqrt (Int.toNat k) ≤ Int.toNat k := Nat.sqrt_le _
  have h_int' : ((Nat.sqrt (Int.toNat k) * Nat.sqrt (Int.toNat k) : ℕ) : ℤ) ≤ (Int.toNat k : ℤ) :=
    Nat.cast_le.mpr h_nat
  have hk_eq : (Int.toNat k : ℤ) = k := Int.toNat_of_nonneg hk
  simpa [Int.sqrt, Nat.cast_mul, hk_eq] using h_int'

/-- For a nonnegative integer `k`, `k < (Int.sqrt k + 1) * (Int.sqrt k + 1)`.
This is the tight lower bound: the next integer larger than the floor sqrt
squared strictly exceeds `k`. -/
lemma lt_succ_mul_succ_sqrt (k : Int) (hk : 0 ≤ k) : k < (Int.sqrt k + 1) * (Int.sqrt k + 1) := by
  have h_nat : Int.toNat k < (Nat.sqrt (Int.toNat k) + 1) * (Nat.sqrt (Int.toNat k) + 1) :=
    Nat.lt_succ_sqrt _
  have h_int' : (Int.toNat k : ℤ) < (((Nat.sqrt (Int.toNat k) + 1) * (Nat.sqrt (Int.toNat k) + 1) : ℕ) : ℤ) :=
    Nat.cast_lt.mpr h_nat
  have hk_eq : (Int.toNat k : ℤ) = k := Int.toNat_of_nonneg hk
  simpa [Int.sqrt, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hk_eq] using h_int'

/-- For a positive integer `n`, the integer square root satisfies three tight bounds:
`0 ≤ Int.sqrt n`, `(Int.sqrt n)² ≤ n`, and `n < (Int.sqrt n + 1)²`.
This bundles `sqrt_nonneg`, `sqrt_mul_self_le`, and `lt_succ_mul_succ_sqrt`
into a single lemma convenient for case analysis. -/
lemma sqrt_bounds (n : ℤ) (hn : 0 < n) :
    0 ≤ Int.sqrt n ∧ Int.sqrt n * Int.sqrt n ≤ n ∧ n < (Int.sqrt n + 1) * (Int.sqrt n + 1) := by
  have hn' : 0 ≤ n := by omega
  exact ⟨Int.sqrt_nonneg n, sqrt_mul_self_le n hn', lt_succ_mul_succ_sqrt n hn'⟩

/-- If `n` is positive, `q` is nonnegative, and `(q+1)²` already exceeds `n`,
then `Int.sqrt n ≤ q`. This is an upper-bound corollary of `sqrt_bounds`:
if `q+1` would be too large as a floor sqrt, then the true floor sqrt is at most `q`. -/
lemma sqrt_le_of_upper_bound (n q : ℤ) (hn : 0 < n) (hq : 0 ≤ q)
    (hupper : n < (q + 1) * (q + 1)) : Int.sqrt n ≤ q := by
  have hb := sqrt_bounds n hn
  by_contra hnot
  have hstep : q + 1 ≤ Int.sqrt n := by omega
  nlinarith [hb.2.1]

/-- If `0 ≤ n`, `0 < m`, and `n < m * m`, then `Int.sqrt n < m`.
This is a corollary of `sqrt_mul_self_le`: if `Int.sqrt n ≥ m`, then
`n ≥ (Int.sqrt n)² ≥ m²`, contradicting `n < m²`. -/
lemma sqrt_lt_of_lt_sq {n m : ℤ} (hn : 0 ≤ n) (hm : 0 < m) (h : n < m * m) : Int.sqrt n < m := by
  by_contra! h_ge
  have h_sq_ge : m * m ≤ (Int.sqrt n) * (Int.sqrt n) := by
    nlinarith
  have h_sq_le_n : (Int.sqrt n) * (Int.sqrt n) ≤ n := Int.sqrt_mul_self_le n hn
  nlinarith

/-! ### Binary search midpoint bounds

These lemmas describe the position of the binary search midpoint
`lo + (hi - lo) / 2` within the interval `(lo, hi)` when `lo + 1 < hi`. -/

/-- In binary search, when `lo + 1 < hi`, the midpoint `lo + (hi - lo) / 2`
is strictly less than `hi`. -/
lemma mid_lt_right {lo hi : Int} (h : lo + 1 < hi) : lo + (hi - lo) / 2 < hi := by
  have h_div : (hi - lo) / 2 < hi - lo := by
    rw [Int.ediv_lt_iff_lt_mul (by norm_num : (0 : ℤ) < 2)]
    nlinarith
  omega

/-- In binary search, when `lo + 1 < hi`, `lo` is strictly less than the midpoint
`lo + (hi - lo) / 2`. -/
lemma lt_mid_left {lo hi : Int} (h : lo + 1 < hi) : lo < lo + (hi - lo) / 2 := by
  have h_diff : 1 < hi - lo := by omega
  have h_div : 1 ≤ (hi - lo) / 2 :=
    Int.le_ediv_of_mul_le (by norm_num : (0 : ℤ) < 2) (by omega)
  omega

/-! ### Triangular numbers -/

/-- The triangular number `T_{x-1} = x*(x-1)/2`.
Also equals the number of 2-element subsets of an `x`-element set (`C(x,2)`). -/
def triangular (x : Int) : Int :=
  x * (x - 1) / 2

/-- The `k`-th triangular number: `T_k = k * (k + 1) / 2`.
This is the sum `1 + 2 + … + k` and generalizes to negative `k`
by the same closed form. Related to `triangular` by `triangular_number k = triangular (k + 1)`. -/
def triangularNumber_specificDuplicate (k : Int) : Int :=
  k * (k + 1) / 2

/-- `triangularNumber_specificDuplicate k` equals `triangular (k + 1)`:
both compute `k*(k+1)/2` (by associativity/commutativity of multiplication). -/
lemma triangularNumber_eq_triangular_succ (k : Int) : triangularNumber_specificDuplicate k = triangular (k + 1) := by
  unfold triangularNumber_specificDuplicate triangular
  ring

/-! ### Arithmetic series

`arithmeticSeries start count` computes the sum of `count` consecutive integers
starting at `start` (with difference 1). Formally, it equals
`start + (start+1) + … + (start+count-1)` and is given by the closed form
`count * (2*start + count - 1) / 2`. -/

/-- Sum of `count` consecutive integers starting from `start` (step 1).
Closed form: `count * (2*start + count - 1) / 2`.
For example, `arithmeticSeries 1 n = sum_range 1 n = 1 + 2 + … + n = n*(n+1)/2`. -/
def arithmeticSeries (start count : Int) : Int :=
  count * (2 * start + count - 1) / 2

/-- The empty arithmetic series (count = 0) sums to 0. -/
@[simp]
lemma arithmeticSeries_zero (start : Int) : arithmeticSeries start 0 = 0 := by
  unfold arithmeticSeries; ring

/-! ### Ceiling midpoint binary search

These lemmas use the ceiling midpoint formula `(lo + hi + 1) / 2`,
which appears in binary search variants that search for the largest element
satisfying a predicate. -/

/-- In ceiling midpoint binary search, when `lo ≤ hi`,
the midpoint `(lo + hi + 1) / 2` is at most `hi`. -/
lemma mid_ceil_le_hi (lo hi : Int) (h : lo ≤ hi) : (lo + hi + 1) / 2 ≤ hi := by
  omega

/-- In ceiling midpoint binary search, when `lo < hi`,
we have `lo ≤ (lo + hi + 1) / 2 - 1`.
This ensures the search makes progress when the midpoint is too high. -/
lemma lo_le_mid_ceil_sub_one (lo hi : Int) (h : lo < hi) : lo ≤ (lo + hi + 1) / 2 - 1 := by
  have h_ineq : 2 * lo + 2 ≤ lo + hi + 1 := by omega
  have hdiv : (2 * lo + 2) / 2 ≤ (lo + hi + 1) / 2 :=
    Int.ediv_le_ediv (by norm_num) h_ineq
  have hleft : (2 * lo + 2) / 2 = lo + 1 := by
    calc
      (2 * lo + 2) / 2 = (2 * (lo + 1)) / 2 := by ring
      _ = lo + 1 := by
        simpa using Int.mul_ediv_cancel_left (lo + 1) (by norm_num : (2 : ℤ) ≠ 0)
  rw [hleft] at hdiv
  omega

/-- Binary search to find the largest integer `x` in `[lo, hi]` such that `f x ≤ target`.
Uses ceiling midpoint `(lo + hi + 1) / 2` to make progress and avoid infinite loops.
Correctness assumes `f` is monotonic non-decreasing (`findLargest_spec`). -/
def findLargest (f : Int → Int) (target lo hi : Int) : Int :=
  if lo ≥ hi then
    lo
  else
    let mid := (lo + hi + 1) / 2
    if f mid ≤ target then
      findLargest f target mid hi
    else
      findLargest f target lo (mid - 1)
termination_by Int.toNat (hi - lo)

/-- Correctness specification for `findLargest`:
if `f lo ≤ target < f (hi+1)` and `lo ≤ hi`, then the result `r` satisfies:
- `lo ≤ r ≤ hi`
- `f r ≤ target < f (r+1)` -/
lemma findLargest_spec (f : Int → Int) (target lo hi : Int) (h_lo : f lo ≤ target) (h_hi : f (hi + 1) > target)
    (h_le : lo ≤ hi) :
    lo ≤ findLargest f target lo hi ∧ findLargest f target lo hi ≤ hi ∧ f (findLargest f target lo hi) ≤ target ∧ target < f (findLargest f target lo hi + 1) := by
  set motive : Int → Int → Prop := λ lo' hi' =>
    (lo' ≤ hi' → f lo' ≤ target → f (hi' + 1) > target →
      lo' ≤ findLargest f target lo' hi' ∧ findLargest f target lo' hi' ≤ hi' ∧ f (findLargest f target lo' hi') ≤ target ∧ target < f (findLargest f target lo' hi' + 1))
  with hmotive
  refine (findLargest.induct f target motive ?case1 ?case2 ?case3 lo hi) h_le h_lo h_hi
  · intro lo' hi' h_ge h_le' h_lo' h_hi'
    have heq : lo' = hi' := by omega
    have hm : findLargest f target lo' hi' = lo' := by
      unfold findLargest; simp [h_ge]
    rw [hm]
    have h_hi'' : f (lo' + 1) > target := by
      rw [← heq] at h_hi'
      exact h_hi'
    exact ⟨le_rfl, by rw [heq], h_lo', h_hi''⟩
  · intro lo' hi' h_lt mid h_f_mid ih_motive h_le' h_lo' h_hi'
    have h_lt' : lo' < hi' := by omega
    have h_mid_le_hi : mid ≤ hi' := mid_ceil_le_hi lo' hi' (by omega)
    have hm : findLargest f target lo' hi' = findLargest f target mid hi' := by
      rw [findLargest]; simp [h_lt, h_f_mid, mid]
    rw [hm]
    have ih_res := ih_motive h_mid_le_hi h_f_mid h_hi'
    rcases ih_res with ⟨h1, h2, h3, h4⟩
    have h_lo_le_res : lo' ≤ findLargest f target mid hi' := by
      have h_lo_lt_mid : lo' < mid := by
        have : lo' ≤ mid - 1 := lo_le_mid_ceil_sub_one lo' hi' h_lt'
        omega
      omega
    exact ⟨h_lo_le_res, h2, h3, h4⟩
  · intro lo' hi' h_lt mid h_not_f_mid ih_motive h_le' h_lo' h_hi'
    have h_lt' : lo' < hi' := by omega
    have h_f_mid_gt : target < f mid := by omega
    have h_lo_le_midm1 : lo' ≤ mid - 1 :=
      lo_le_mid_ceil_sub_one lo' hi' h_lt'
    have h_f_midm1_add_one_gt : f ((mid - 1) + 1) > target := by
      have : (mid - 1) + 1 = mid := by omega
      rw [this]
      omega
    have hm : findLargest f target lo' hi' = findLargest f target lo' (mid - 1) := by
      rw [findLargest]; simp [h_lt, h_not_f_mid, mid]
    rw [hm]
    have ih_res := ih_motive h_lo_le_midm1 h_lo' h_f_midm1_add_one_gt
    rcases ih_res with ⟨h1, h2, h3, h4⟩
    have h_res_le_hi : findLargest f target lo' (mid - 1) ≤ hi' := by
      have h_mid_le_hi : mid ≤ hi' := mid_ceil_le_hi lo' hi' (by omega)
      omega
    exact ⟨h1, h_res_le_hi, h3, h4⟩

/-! ### Max/Min lemmas for ℤ

These lemmas exploit the discreteness of `ℤ`: distinct integers bounded below
differ by at least 1, giving a +1 or -1 tight bound on `max`/`min`. -/

/-- If `lb ≤ x`, `lb ≤ y`, and `x ≠ y`, then `lb + 1 ≤ max x y`.
Because `ℤ` is discrete, the larger of two distinct integers both ≥ `lb`
must be at least `lb + 1`. -/
lemma add_one_le_max_of_ne {x y lb : ℤ} (hx : lb ≤ x) (hy : lb ≤ y) (hne : x ≠ y) : lb + 1 ≤ max x y := by
  by_cases h : x < y
  · have hmax : max x y = y := max_eq_right (by omega)
    rw [hmax]
    omega
  · have hmax : max x y = x := max_eq_left (by omega)
    rw [hmax]
    omega

/-! ### Integer subtraction under strict inequality -/

/-- If `a < b` in `ℤ`, then `b - a ≥ 1`. This is the discrete integer analog of
`sub_pos.mpr` (which gives `0 < b - a`); for integers, any strictly positive integer
is at least `1`. -/
lemma sub_ge_one_of_lt {a b : Int} (h : a < b) : b - a ≥ 1 := by
  omega

/-! ### Divisor search -/

/-- Find the first divisor of `n` starting from `d` (inclusive). Returns `n` if no divisor
strictly between `d` and `n` (exclusive) is found — since `n` always divides `n`.
This is a recursive scan upward from `d`, testing divisibility with `n % d = 0`.

When `d = 2`, this finds the smallest divisor ≥ 2 of `n`, which is useful for
prime factorization (`smallest_prime_divisor n := first_divisor_from n 2`).

The function terminates because `d` strictly increases toward `n` on each recursive
call, and the base case `d ≥ n` is reached in finitely many steps. -/
def first_divisor_from (n d : Int) : Int :=
  if d ≥ n then
    n
  else if n % d = 0 then
    d
  else
    first_divisor_from n (d + 1)
termination_by (n - d).toNat

/-- Count the number of positive divisors of `n` that are ≥ `d` (and ≤ `n`).
Scans upward from `d`, testing `n % d = 0` at each step. Stops when `d ≤ 0` or `n < d`.
Returns an `Int` count (always nonnegative under standard preconditions: `1 ≤ d` and `n ≥ d`).

This is useful for problems involving number of divisors, such as "count numbers with exactly
4 divisors" (LeetCode 1390). -/
def countDivisorsFrom (n d : Int) : Int :=
  if d ≤ 0 ∨ n < d then 0
  else if n % d = 0 then 1 + countDivisorsFrom n (d + 1)
  else countDivisorsFrom n (d + 1)
termination_by (n - d + 1).toNat

/-- Sum the positive divisors of `n` that are ≥ `d` (and ≤ `n`).
Scans upward from `d`, testing `n % d = 0` at each step. When a divisor is found,
adds it to the running sum. Stops when `d ≤ 0` or `n < d`.

This is useful for problems involving sum of divisors, such as "sum all divisors
of numbers with exactly 4 divisors" (LeetCode 1390). -/
def sumDivisorsFrom (n d : Int) : Int :=
  if d ≤ 0 ∨ n < d then 0
  else if n % d = 0 then d + sumDivisorsFrom n (d + 1)
  else sumDivisorsFrom n (d + 1)
termination_by (n - d + 1).toNat

/-! ### Absolute difference

`abs_diff a b = max (a - b) (b - a)` is an alternative formulation of `|a - b|`
that does not require `Abs` and is often more convenient for case analysis and
`omega`-style proofs. When `a < b`, it simplifies to `b - a`. -/

/-- `abs_diff a b = max (a - b) (b - a)`. This equals `|a - b|` and is always nonnegative.
Works for any `LinearOrderedAddCommGroup`. -/
def abs_diff {α : Type _} [LinearOrderedAddCommGroup α] (a b : α) : α :=
  max (a - b) (b - a)

/-! ### `abs_diff_eq` — Bool predicate for absolute difference equality

`abs_diff_eq a b k` is true iff `a - b = k` or `b - a = k`, i.e., the absolute
difference between `a` and `b` equals `k`. This is a `Bool`-valued companion to
`abs_diff` that is convenient for `decide`-based reasoning and for use with list
operations like `filter`, `any`, and `countPz`.

Works for any `AddGroup` with `DecidableEq`. -/

/-- Bool predicate: `abs_diff_eq a b k` is true iff `|a - b| = k`, i.e.,
`a - b = k` or `b - a = k`. -/
def abs_diff_eq {α : Type _} [AddGroup α] [DecidableEq α] (a b k : α) : Bool :=
  decide (a - b = k ∨ b - a = k)

/-- `abs_diff_eq` is symmetric: `abs_diff_eq a b k = abs_diff_eq b a k`. -/
lemma abs_diff_eq_comm {α : Type _} [AddGroup α] [DecidableEq α] (a b k : α) :
    abs_diff_eq a b k = abs_diff_eq b a k := by
  simp [abs_diff_eq, eq_comm, or_comm]

/-- `abs_diff_eq` is reflexive at zero: `abs_diff_eq a a 0` is true. -/
@[simp]
lemma abs_diff_eq_self_zero {α : Type _} [AddGroup α] [DecidableEq α] (a : α) :
    abs_diff_eq a a 0 := by
  simp [abs_diff_eq]

/-- When `abs_diff_eq a b k` is true, then at least one of `a - b = k` or `b - a = k`
holds (in `Prop`). This bridges the `Bool` predicate to propositional reasoning. -/
lemma abs_diff_eq_true_iff {α : Type _} [AddGroup α] [DecidableEq α] (a b k : α) :
    abs_diff_eq a b k = true ↔ a - b = k ∨ b - a = k := by
  simp [abs_diff_eq]

/-- `abs_diff` is commutative: `abs_diff a b = abs_diff b a`. -/
lemma abs_diff_comm {α : Type _} [LinearOrderedAddCommGroup α] (a b : α) : abs_diff a b = abs_diff b a := by
  rw [abs_diff, abs_diff, max_comm]

/-- If `a < b`, then `abs_diff a b = b - a`.
This is the main simplification: when `a < b`, the max-based absolute difference
reduces to the positive difference `b - a` (since `a - b` is negative). -/
lemma abs_diff_eq_sub_of_lt {α : Type _} [LinearOrderedAddCommGroup α] {a b : α} (h : a < b) :
    abs_diff a b = b - a := by
  rw [abs_diff]
  apply max_eq_right
  have hle : a - b ≤ b - a := by
    have hnonpos : a - b ≤ 0 := sub_nonpos.mpr (le_of_lt h)
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt h)
    exact le_trans hnonpos hnonneg
  exact hle

/-- If `a < b`, then `abs_diff b a = b - a`.
This is the "swapped" version of `abs_diff_eq_sub_of_lt`, obtained by commuting
`abs_diff` then applying the main lemma. -/
lemma abs_diff_eq_sub_of_lt' {α : Type _} [LinearOrderedAddCommGroup α] {a b : α} (h : a < b) :
    abs_diff b a = b - a := by
  rw [abs_diff_comm, abs_diff_eq_sub_of_lt h]

/-- `abs_diff a b` equals `|a - b|`, the standard absolute value of the difference.
This lemma connects the `max`-based formulation to the `abs`-notation form,
allowing users to switch between the two representations. -/
lemma abs_diff_eq_abs_sub {α : Type _} [LinearOrderedAddCommGroup α] (a b : α) : abs_diff a b = |a - b| := by
  rw [abs_diff, abs_eq_max_neg, neg_sub]

/-- `abs_diff a a = 0`: the absolute difference of a value with itself is zero.
This follows from `abs_diff_eq_abs_sub` and the fact that `|0| = 0`. -/
@[simp]
lemma abs_diff_self {α : Type _} [LinearOrderedAddCommGroup α] (a : α) : abs_diff a a = 0 := by
  rw [abs_diff_eq_abs_sub, sub_self, abs_zero]

/-- `abs_diff` is always nonnegative: `0 ≤ abs_diff a b`.
Since `abs_diff a b = max (a - b) (b - a)`, one of the two differences
is always ≥ 0 (they sum to zero), so the max is ≥ 0.
This follows directly from `abs_diff_eq_abs_sub` and `abs_nonneg`. -/
lemma abs_diff_nonneg {α : Type _} [LinearOrderedAddCommGroup α] (a b : α) : 0 ≤ abs_diff a b := by
  rw [abs_diff_eq_abs_sub]
  exact abs_nonneg _

/-- If both `a` and `b` lie in the integer interval `[0, n)`, then their absolute difference
is also bounded by `n`. This is a key lemma for bounding positional differences in array
index arithmetic where indices are nonnegative and less than the array length. -/
lemma abs_diff_lt_bound {a b n : ℤ} (ha0 : 0 ≤ a) (ha : a < n) (hb0 : 0 ≤ b) (hb : b < n) :
    abs_diff a b < n := by
  rw [abs_diff_eq_abs_sub]
  apply abs_lt.mpr
  constructor
  · omega
  · omega

/-! ### Nat.cast of `min` lemmas for ℤ

These lemmas bridge `Nat.min` to `Int.min` via `Nat.cast`. They are convenience wrappers
around mathlib's `Nat.cast_min`, `min_le_left`, and `min_le_right` for the common case
of casting `Nat` comparisons to `Int`. -/

/-- The integer cast of the minimum of two naturals equals the minimum of their integer casts.
This is a convenience wrapper around `Nat.cast_min`. -/
lemma nat_min_cast_eq_int_min (x y : Nat) :
    ((min x y : Nat) : Int) = min (x : Int) (y : Int) :=
  Nat.cast_min x y

/-- The integer cast of `min x y` is ≤ the integer cast of the left argument `x`. -/
lemma nat_min_cast_le_left (x y : Nat) : ((min x y : Nat) : Int) ≤ (x : Int) := by
  exact_mod_cast min_le_left x y

/-- The integer cast of `min x y` is ≤ the integer cast of the right argument `y`. -/
lemma nat_min_cast_le_right (x y : Nat) : ((min x y : Nat) : Int) ≤ (y : Int) := by
  exact_mod_cast min_le_right x y

/-! ### Bounded linear search on `ℤ`

`searchFrom p start n` finds the smallest `i` with `start ≤ i ≤ start + n` such that `p i` holds.
Returns `start + n` if no such `i` exists. This is the `ℤ` analog of `Nat.findFrom`,
using `Prop` predicates with `DecidablePred` instead of `Bool`, which is more convenient
for inductive proofs about search procedures. -/

/-- Bounded linear search on `ℤ`: find the smallest `i` with `start ≤ i ≤ start + n` such that
`p i` holds. Returns `start + n` if no such `i` exists. The search steps by `+1` from `start`
upward, checking at most `n+1` positions. -/
def searchFrom (p : Int → Prop) [DecidablePred p] (start : Int) : Nat → Int
  | 0 => start
  | n+1 =>
    if p start then start
    else searchFrom p (start + 1) n

/-- Lower bound: `start ≤ searchFrom p start n`. -/
lemma searchFrom_lower_bound (p : Int → Prop) [DecidablePred p] (start : Int) (n : Nat) :
    start ≤ searchFrom p start n := by
  induction n generalizing start with
  | zero => simp [searchFrom]
  | succ n ih =>
    simp [searchFrom]
    split
    · simp
    · have h := ih (start + 1)
      omega

/-- Upper bound: `searchFrom p start n ≤ start + n`. -/
lemma searchFrom_upper_bound (p : Int → Prop) [DecidablePred p] (start : Int) (n : Nat) :
    searchFrom p start n ≤ start + (n : ℤ) := by
  induction n generalizing start with
  | zero => simp [searchFrom]
  | succ n ih =>
    simp [searchFrom]
    split
    · omega
    · have h := ih (start + 1)
      omega

/-- For all `k` with `start ≤ k < searchFrom p start n`, `p k` is false. -/
lemma searchFrom_fail_before (p : Int → Prop) [DecidablePred p] (start : Int) (n : Nat) (k : Int)
    (hk_ge_start : start ≤ k) (hk_lt_r : k < searchFrom p start n) :
    ¬ p k := by
  induction n generalizing start with
  | zero =>
    simp [searchFrom] at hk_lt_r
    omega
  | succ n ih =>
    simp [searchFrom] at hk_lt_r ⊢
    by_cases hp_start : p start
    · simp [hp_start] at hk_lt_r
      omega
    · simp [hp_start] at hk_lt_r ⊢
      by_cases hk_eq_start : k = start
      · subst k
        exact hp_start
      · have hk_ge_start1 : start + 1 ≤ k := by omega
        exact ih (start := start + 1) hk_ge_start1 hk_lt_r

/-- If there exists `k` in `[start, start + n]` with `p k` true, then
`searchFrom p start n` returns a value that satisfies `p`. -/
lemma searchFrom_satisfies (p : Int → Prop) [DecidablePred p] (start : Int) (n : Nat)
    (h_exists : ∃ k, start ≤ k ∧ k ≤ start + (n : ℤ) ∧ p k) :
    p (searchFrom p start n) := by
  induction n generalizing start with
  | zero =>
    simp [searchFrom]
    rcases h_exists with ⟨k, hk_start, hk_ub, hk_p⟩
    have hk_eq_start : k = start := by omega
    subst k
    exact hk_p
  | succ n ih =>
    simp [searchFrom]
    by_cases hp_start : p start
    · simp [hp_start]
    · simp [hp_start]
      rcases h_exists with ⟨k, hk_start, hk_ub, hk_p⟩
      have hk_ge_start1 : start + 1 ≤ k := by
        by_contra! hlt
        have hk_eq_start : k = start := by omega
        subst k
        exact hp_start hk_p
      have hk_ub' : k ≤ (start + 1) + (n : ℤ) := by omega
      exact ih (start := start + 1) ⟨k, hk_ge_start1, hk_ub', hk_p⟩

/-! ### Bounded downward search on `ℤ`

`searchDown p n` finds the largest `k` with `1 ≤ k ≤ n` such that `p (k : Int)` holds.
Returns `-1` if no such `k` exists. This is the dual of `searchFrom`: while `searchFrom`
searches upward to find the smallest satisfying index, `searchDown` searches downward
to find the largest satisfying index. The search steps by `-1` from `n` down to `1`,
checking at most `n` positions. -/

/-- Bounded downward search on `ℤ`: find the largest `k` with `1 ≤ k ≤ n` such that
`p (k : Int)` holds. Returns `-1` if no such `k` exists. Scans downward from `n` to `1`. -/
def searchDown (p : Int → Prop) [DecidablePred p] : Nat → Int
  | 0 => -1
  | k+1 => if p ((k+1 : Nat) : Int) then ((k+1 : Nat) : Int) else searchDown p k

/-- Range property of `searchDown`: the result is either `-1` or lies between `1` and `n`
(inclusive). This characterizes where the result can be. -/
lemma searchDown_range (p : Int → Prop) [DecidablePred p] (n : Nat) :
    searchDown p n = -1 ∨ (1 ≤ searchDown p n ∧ searchDown p n ≤ (n : Int)) := by
  induction' n with k ih
  · unfold searchDown; left; rfl
  · unfold searchDown
    by_cases h : p ((k+1 : Nat) : Int)
    · rw [if_pos h]
      right
      have hpos : (1 : Int) ≤ ((k+1 : Nat) : Int) := by
        have : (1 : Nat) ≤ k+1 := by omega
        exact Nat.cast_le.mpr this
      exact ⟨hpos, le_rfl⟩
    · rw [if_neg h]
      rcases ih with (hneg | hpos)
      · left; exact hneg
      · right; rcases hpos with ⟨h1, h2⟩
        have h2' : searchDown p k ≤ ((k+1 : Nat) : Int) := by
          have : (k : Int) ≤ ((k+1 : Nat) : Int) := by omega
          omega
        exact ⟨h1, h2'⟩

/-- Soundness of `searchDown`: if the result is nonnegative, then `p` holds at that result.
This is the fundamental correctness property. -/
lemma searchDown_sound (p : Int → Prop) [DecidablePred p] (n : Nat) :
    searchDown p n ≥ 0 → p (searchDown p n) := by
  induction' n with k ih
  · unfold searchDown; intro h; linarith
  · unfold searchDown
    by_cases h : p ((k+1 : Nat) : Int)
    · rw [if_pos h]; intro; exact h
    · rw [if_neg h]; exact ih

/-- Completeness of `searchDown`: if the result is `-1`, then no `x` in `1 ≤ x ≤ n` satisfies `p`.
This is the "failure implies nothing found" property. -/
lemma searchDown_complete (p : Int → Prop) [DecidablePred p] (n : Nat) :
    searchDown p n = -1 → (∀ x : Int, 1 ≤ x → x ≤ (n : Int) → ¬ p x) := by
  induction' n with k ih
  · unfold searchDown; intro h; intro x hx1 hx2; omega
  · unfold searchDown
    by_cases h_eq : p ((k+1 : Nat) : Int)
    · rw [if_pos h_eq]
      intro hcontra
      have hpos : (1 : Int) ≤ ((k+1 : Nat) : Int) := by
        have : (1 : Nat) ≤ k+1 := by omega
        exact Nat.cast_le.mpr this
      omega
    · rw [if_neg h_eq]
      intro hneg
      have h_forall := ih hneg
      intro x hx1 hx2
      by_cases hx_eq : x = ((k+1 : Nat) : Int)
      · rw [hx_eq]; exact h_eq
      · have hx_le_k : x ≤ (k : Int) := by omega
        exact h_forall x hx1 hx_le_k

/-! ### Digit extraction in arbitrary base

`digitInBase num base pos` extracts the digit at position `pos` (0 = units, 1 = base-val, etc.)
of integer `num` in the given `base`. Computes `(num / base^pos) % base`.

`decimal_digit num pos` is the specialization to base 10:
the digit at decimal position `pos` (0 = units, 1 = tens, etc.). -/

/-- The digit at position `pos` (0 = units, 1 = base-val, etc.) of integer `num`
    in base `base`. Formally: `(num / base^pos) % base`. -/
def digitInBase (num base : Int) (pos : Nat) : Int :=
  (num / (base ^ pos)) % base

/-- The decimal digit at position `pos` (0 = units, 1 = tens, etc.) of an integer.
    This is `digitInBase num 10 pos`. -/
def decimal_digit (num : Int) (pos : Nat) : Int :=
  digitInBase num 10 pos

/-! ### Argmax over a 1-indexed integer range

`best_val_in_range f n` finds the integer `t` in `[1, n]` (as `Int`) that maximizes
`f t : β`. If `n = 0`, returns `1`. Ties go to the earlier value (lower `t`).

This is the argmax analog of `maxOverRange_specificDuplicate` (from `Nat`): while `maxOverRange_specificDuplicate` returns
the maximum *value*, `best_val_in_range` returns the *argument* that achieves it. -/

/-- The integer `t ∈ [1, n]` that maximizes `f t : β`. Returns `1` when `n = 0`.
Ties are broken in favor of the smaller `t`. -/
def best_val_in_range {β : Type _} [LinearOrder β] (f : Int → β) (n : Nat) : Int :=
  Nat.rec (1 : Int) (λ k prev =>
    let t := (k+1 : Int)
    if f t > f prev then t else prev
  ) n

/-- `best_val_in_range` always returns a value at least `1`.
This follows because the base case is `1` and the recursion only replaces `prev`
with `t = k+1 ≥ 1`. -/
lemma best_val_in_range_lower {β : Type _} [LinearOrder β] (f : Int → β) (n : Nat) :
    1 ≤ best_val_in_range f n := by
  induction' n with k ih
  · unfold best_val_in_range; dsimp; omega
  · unfold best_val_in_range
    dsimp
    split_ifs with h
    · omega
    · exact ih
/-! ### Population count (Hamming weight)

`popcountAux x acc` computes `popcount x + acc` by recursively dividing `x` by 2
and accumulating the least significant bit (`x % 2`) into `acc`. `popcount x` returns
the number of set bits (ones) in the binary representation of `x`.

When `x ≤ 0`, returns `acc` (or `0` for `popcount`), which is consistent with
the convention that non-positive integers have population count 0.

Generalized from `popcount_helper` / `popcount` (LeetCode 762). -/

/-- Tail-recursive helper for `popcount`. Computes `popcount x + acc` for integers. -/
def popcountAux (x acc : Int) : Int :=
  if x ≤ 0 then
    acc
  else
    popcountAux (x / 2) (acc + (x % 2))
termination_by x.toNat

/-- Population count (Hamming weight) for integers: the number of 1-bits in the binary
representation of `x`. For `x ≤ 0`, returns `0`. -/
def popcount (x : Int) : Int :=
  popcountAux x 0

end Int
