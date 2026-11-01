import Mathlib
import general.Char.BalancedDelimiters
import general.Common.Order

namespace Nat

/-! ### Minimal existence -/

/-- If a predicate on `Nat` is nonempty, there exists a minimal number satisfying it. -/
lemma exists_minimal {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
    set n := Nat.find h with hn
    have hnP : P n := Nat.find_spec h
    have hmin (m : Nat) (hm : P m) : n ≤ m := Nat.find_min' h hm
    exact ⟨n, hnP, hmin⟩

/-- `Nat.find` is independent of the specific existence proof:
two proofs of the same existential give the same `Nat.find`. -/
lemma find_irrel {P : Nat → Prop} [DecidablePred P] (hex1 hex2 : ∃ x : Nat, P x) :
    Nat.find hex1 = Nat.find hex2 := by
  apply (Nat.find_eq_iff hex1).mpr
  constructor
  · exact Nat.find_spec hex2
  · intro m hm
    exact Nat.find_min hex2 hm

/-! ### Basic arithmetic decompositions -/

/-- Decompose `n` into its even part `(n/2)*2` plus the parity indicator `(if n%2=1 then 1 else 0)`.
This is a restructured form of `Nat.div_add_mod n 2`, useful when treating even and odd
contributions separately. -/
lemma even_part_add_odd_indicator_eq_self (n : Nat) : (n / 2) * 2 + (if n % 2 = 1 then 1 else 0) = n := by
  have hmod := Nat.mod_two_eq_zero_or_one n
  rcases hmod with (h0 | h1)
  · rw [h0]; simp
    have := Nat.div_add_mod n 2
    rw [h0] at this
    omega
  · rw [h1]; simp
    have := Nat.div_add_mod n 2
    rw [h1] at this
    omega

/-- Arithmetic identity for the length of an inclusive range:
when `a ≤ b`, we have `a + (b - a + 1) = b + 1`. -/
lemma add_sub_add_one (h : a ≤ b) : a + (b - a + 1) = b + 1 := by
  calc
    a + (b - a + 1) = (a + (b - a)) + 1 := by rw [← Nat.add_assoc]
    _ = b + 1 := by rw [Nat.add_sub_cancel' h]

/-- Identity for reconstructing a sum from differences: given `x ≤ a` and `x ≤ b`,
`(a - x) + (b - x) + 2 * x = a + b`. This is useful when both `a` and `b` have a
common subtrahend `x` and you need to relate the subtracted forms back to the original sum.
For example, if each of two counts loses `x` items, the total can be expressed
as `(countA - x) + (countB - x) + 2*x = countA + countB`. -/
lemma sub_add_sub_eq_add_two_mul (a b x : Nat) (hax : x ≤ a) (hbx : x ≤ b) :
    (a - x) + (b - x) + (2 * x) = a + b := by
  have ha : (a - x) + x = a := Nat.sub_add_cancel hax
  have hb : (b - x) + x = b := Nat.sub_add_cancel hbx
  calc
    (a - x) + (b - x) + (2 * x) = (a - x) + (b - x) + (x + x) := by rw [Nat.two_mul]
    _ = ((a - x) + x) + ((b - x) + x) := by omega
    _ = a + b := by rw [ha, hb]

/-- For any natural numbers `n` and `d`, `n = (n / d) * d + n % d`.
This is the commuted form of `Nat.div_add_mod`, with the quotient multiplied
on the left side of the product. -/
lemma div_mul_add_mod (n d : Nat) : n = (n / d) * d + n % d := by
  have h := (Nat.div_add_mod n d).symm
  calc
    n = d * (n / d) + n % d := h
    _ = (n / d) * d + n % d := by rw [Nat.mul_comm d (n / d)]


end Nat

namespace Nat

/-! ### Evenness / parity -/

/-- `isEven n` returns `true` iff `n` is even, i.e., `n % 2 = 0`. -/
def isEven (n : Nat) : Bool :=
  n % 2 = 0


lemma isEven_zero : isEven 0 = true := by
  simp [isEven]


lemma isEven_one : isEven 1 = false := by
  simp [isEven]

lemma isEven_iff (n : Nat) : isEven n ↔ n % 2 = 0 := by
  simp [isEven]

lemma isEven_eq_true_iff (n : Nat) : isEven n = true ↔ n % 2 = 0 := by
  simp [isEven]

lemma isEven_eq_false_iff (n : Nat) : isEven n = false ↔ n % 2 ≠ 0 := by
  simp [isEven]

lemma not_isEven_iff (n : Nat) : ¬ isEven n ↔ n % 2 ≠ 0 := by
  simp [isEven]

end Nat


namespace Nat

/-! ### Parity (mod two) -/

/-- If `n % 2 ≠ 1`, then `n % 2 = 0`. This is the contrapositive of the "or" branch
in `Nat.mod_two_eq_zero_or_one`. -/
lemma mod_two_eq_zero_of_ne_one {n : Nat} (h : n % 2 ≠ 1) : n % 2 = 0 := by
  have hm := Nat.mod_two_eq_zero_or_one n
  rcases hm with (h0 | h1)
  · exact h0
  · exfalso; exact h h1

/-- If `n % 2 ≠ 0`, then `n % 2 = 1`. The mirror of `mod_two_eq_zero_of_ne_one`. -/
lemma mod_two_eq_one_of_ne_zero {n : Nat} (h : n % 2 ≠ 0) : n % 2 = 1 := by
  have hm := Nat.mod_two_eq_zero_or_one n
  rcases hm with (h0 | h1)
  · exfalso; exact h h0
  · exact h1

/-- When `n / 2 = 0` and `n ≠ 0`, then `n` must be exactly 1. -/
lemma eq_one_of_div_two_eq_zero_and_ne_zero {n : Nat} (hdiv : n / 2 = 0) (hne : n ≠ 0) :
    n = 1 := by
  have hm1 : n % 2 = 1 := by
    have hmod_ne_zero : n % 2 ≠ 0 := by
      intro hzero
      have := Nat.div_add_mod n 2
      rw [hdiv, hzero] at this
      exact hne (by omega)
    exact mod_two_eq_one_of_ne_zero hmod_ne_zero
  have := Nat.div_add_mod n 2
  rw [hdiv, hm1] at this
  omega

/-- If `n` is even (`n % 2 = 0`) and `n ≥ 1`, then `n-1` is odd (`(n-1) % 2 = 1`).
This is useful for parity-based case analysis where an even positive number's predecessor
must be odd. -/
lemma even_implies_pred_odd (n : Nat) (h_even : n % 2 = 0) (h_pos : 1 ≤ n) : (n - 1) % 2 = 1 := by
  omega

/-- Adding 2 preserves the value modulo 2: `(n + 2) % 2 = n % 2`.
This is a simple but frequently useful lemma for parity-based reasoning. -/
lemma add_two_mod_two (n : Nat) : (n + 2) % 2 = n % 2 := by
  omega

/-- If two natural numbers are even (divisible by 2), then their bitwise OR is also even. -/
lemma lor_mod_two_eq_zero_of_mod_two_eq_zero {a b : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    (a ||| b) % 2 = 0 := by
  have h_decide_false : decide ((a ||| b) % 2 = 1) = false := by
    calc
      decide ((a ||| b) % 2 = 1) = (a ||| b).testBit 0 := by rw [Nat.testBit_zero]
      _ = (a.testBit 0 || b.testBit 0) := by rw [Nat.testBit_lor]
      _ = (decide (a % 2 = 1) || decide (b % 2 = 1)) := by rw [Nat.testBit_zero, Nat.testBit_zero]
      _ = (false || false) := by simp [ha, hb]
      _ = false := by simp
  have h_not_one : (a ||| b) % 2 ≠ 1 := by
    intro h_eq
    have h_true : decide ((a ||| b) % 2 = 1) = true := decide_eq_true h_eq
    rw [h_decide_false] at h_true
    exact Bool.noConfusion h_true
  have h_lt_two : (a ||| b) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

end Nat



namespace Nat

/-! ### Applying arithmetic operators from characters -/

/-- Apply a single character arithmetic operator to two `Nat` values.
Handles `'+'`, `'-'`, `'*'`, `'/'`; any other operator defaults to returning `a`. -/
def applyArithOp (a : Nat) (op : Char) (b : Nat) : Nat :=
  match op with
  | '+' => a + b
  | '-' => a - b
  | '*' => a * b
  | '/' => a / b
  | _   => a

end Nat


namespace Nat

/-! ### Arithmetic lemmas -/

/-- The absolute difference `Nat.dist a b` is bounded above by `max a b`.
This holds because `Nat.dist a b = (a - b) + (b - a)`, and each term is bounded
by the max of the two numbers. -/
lemma dist_le_max (a b : Nat) : Nat.dist a b ≤ max a b := by
  have hdef : Nat.dist a b = (a - b) + (b - a) := rfl
  rw [hdef]
  by_cases h : a ≤ b
  · have hsub : a - b = 0 := Nat.sub_eq_zero_of_le h
    rw [hsub, zero_add]
    rw [max_eq_right h]
    exact Nat.sub_le _ _
  · have h' : b ≤ a := Nat.le_of_not_le h
    have hsub : b - a = 0 := Nat.sub_eq_zero_of_le h'
    rw [hsub, add_zero]
    rw [max_eq_left h']
    exact Nat.sub_le _ _

/-! ### Minimum distance to a list of positions -/

/-- Minimum natural distance from `x` to any element in `xs`.
Returns `fallback` when `xs` is empty.
This is a fold over the list, taking `Nat.min` of `Nat.dist x y` at each step. -/
def minDistToList (xs : List Nat) (x : Nat) (fallback : Nat) : Nat :=
  xs.foldl (fun acc y => Nat.min acc (Nat.dist x y)) fallback


lemma minDistToList_nil (x fallback : Nat) : minDistToList [] x fallback = fallback := rfl

lemma minDistToList_cons (x y fallback : Nat) (ys : List Nat) :
    minDistToList (y :: ys) x fallback = minDistToList ys x (Nat.min fallback (Nat.dist x y)) := rfl

/-- If `n ≥ 2`, then `1 < n`. This is a convenience lemma bridging from "at least 2"
to "strictly greater than 1", commonly needed when `omega` alone is not used. -/
lemma one_lt_of_two_le {n : Nat} (h : n ≥ 2) : 1 < n := by omega

/-- If `1 < b`, then `0 < b`. A convenience lemma extracting positivity from the
stronger condition `1 < b`. Often used to get `0 < base` for digit/base operations
where termination requires `base > 1`. -/
lemma zero_lt_of_one_lt {b : Nat} (h : 1 < b) : 0 < b :=
  Nat.lt_trans Nat.zero_lt_one h

/-- If `n ≤ a`, then `n ≤ max a b`. A convenience lemma combining `Nat.le_trans`
with `Nat.le_max_left`. -/
lemma le_max_left_of_le {a b n : Nat} (h : n ≤ a) : n ≤ Nat.max a b :=
  le_trans h (Nat.le_max_left _ _)

/-- If `max a b > a`, then `b > a` and `max a b = b`. In other words, the maximum
exceeding the left argument forces the right argument to be strictly larger and
to be the maximum. -/
lemma max_gt_left_imp {a b : Nat} (h : max a b > a) : b > a ∧ max a b = b := by
  have hb_gt : b > a := by
    by_contra! hle
    -- hle : b ≤ a
    have : max a b = a := Nat.max_eq_left hle
    rw [this] at h; exact Nat.lt_irrefl _ h
  exact ⟨hb_gt, Nat.max_eq_right (Nat.le_of_lt hb_gt)⟩

/-- If `0 < a`, then `0 < Nat.max a b`. When the left argument is positive, the
maximum of the two is also positive. Useful for proving denominators and dividend
bounds are nonzero. -/
lemma max_pos_of_pos_left {a b : Nat} (h : 0 < a) : 0 < Nat.max a b :=
  Nat.lt_of_lt_of_le h (Nat.le_max_left a b)

/-- `min a c ≤ max b d` given `a ≤ b`. Useful when merging intervals or bounding
a value between the min of lower bounds and the max of upper bounds. -/
lemma min_le_max_of_le (a b c d : Nat) (hab : a ≤ b) : min a c ≤ max b d :=
  calc
    min a c ≤ a := Nat.min_le_left _ _
    _ ≤ b := hab
    _ ≤ max b d := Nat.le_max_left _ _

/-- If `a + b = c`, then `a ≤ c`. This is a basic consequence of `Nat.add_comm`
and the definition of addition: `c` is `a` plus some nonnegative amount `b`. -/
lemma le_of_add_eq {a b c : Nat} (h : a + b = c) : a ≤ c := by
  omega

/-- If `a + b ≤ c`, then `a ≤ c`. This extracts a left-hand bound from a sum bound.
Useful when a sum bound is given and we need a bound on the individual summand. -/
lemma le_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c :=
  Nat.le_trans (Nat.le_add_right a b) h

/-- If `a / b ≥ r`, then `a ≥ r * b`. This is the contrapositive direction of
`Nat.mul_div_le`: the quotient lower-bounds the dividend divided by the divisor.
Holds even when `b = 0` (since `a / 0 = 0`, so `h : 0 ≥ r` gives `r = 0`,
and then `a ≥ 0` trivially). -/
lemma mul_le_of_div_ge (a b r : Nat) (h : a / b ≥ r) : a ≥ r * b := by
  have h1 : b * (a / b) ≤ a := Nat.mul_div_le a b
  have h2 : r * b ≤ (a / b) * b := Nat.mul_le_mul_right b h
  have h3 : (a / b) * b = b * (a / b) := Nat.mul_comm _ _
  rw [h3] at h2
  exact le_trans h2 h1

/-- If `x ≤ t`, then `x - Nat.min x t = 0`.
This holds because `Nat.min x t = x` when `x ≤ t`, and `x - x = 0`. -/
lemma sub_min_eq_zero_of_le {x t : Nat} (h : x ≤ t) : x - Nat.min x t = 0 := by
  have hm : Nat.min x t = x := Nat.min_eq_left h
  rw [hm, Nat.sub_self]

/-- If `x < Nat.min a b + 1`, then `x ≤ a`.
This is useful for deducing bounds from a `List.range` membership condition:
`x ∈ List.range (Nat.min a b + 1)` implies `x ≤ a`. -/
lemma le_of_lt_min_add_one {x a b : Nat} (h : x < Nat.min a b + 1) : x ≤ a := by
  have hx : x ≤ Nat.min a b := by omega
  have hmin : Nat.min a b ≤ a := Nat.min_le_left _ _
  omega

/-- The sum of two truncated subtractions is bounded by the sum of the originals:
`(a - b) + (c - d) ≤ a + c`. Follows directly from `Nat.sub_le a b : a - b ≤ a`
and `Nat.sub_le c d : c - d ≤ c`. -/
lemma sub_add_sub_le_add (a b c d : Nat) : (a - b) + (c - d) ≤ a + c :=
  Nat.add_le_add (Nat.sub_le a b) (Nat.sub_le c d)

/-- Combined subtraction inequality: if `a ≤ c` and `d ≤ b`, then `a - b ≤ c - d`.
Combines `Nat.sub_le_sub_right` and `Nat.sub_le_sub_left` into a single chain. -/
lemma sub_le_sub {a b c d : Nat} (hac : a ≤ c) (hbd : d ≤ b) : a - b ≤ c - d :=
  calc
    a - b ≤ c - b := Nat.sub_le_sub_right hac b
    _ ≤ c - d := Nat.sub_le_sub_left hbd c

/-- If `j ≤ k` and `x ≤ j`, then `j - x ≤ k`.
Useful for bounding the result of a subtraction when a larger bound is known. -/
lemma sub_le_of_le_sub {j k x : Nat} (hj : j ≤ k) (hx : x ≤ j) : j - x ≤ k := by
  omega

/-- Rearrangement: `(b * A + S) / b = A + S / b` for `b > 0`.
Useful when dividing a linear combination `b * A + S` by `b`:
the quotient `A` factors out, and only the remainder term `S` contributes to the division. -/
lemma div_mul_add_eq_add_div (b A S : Nat) (hb : 0 < b) : (b * A + S) / b = A + S / b := by
  apply Nat.div_eq_of_lt_le
  · -- lower bound: (A + S / b) * b ≤ b * A + S
    calc
      (A + S / b) * b = b * A + b * (S / b) := by ring
      _ ≤ b * A + S := Nat.add_le_add_left (Nat.mul_div_le S b) _
  · -- upper bound: b * A + S < (A + S / b + 1) * b
    have hS_eq : S = b * (S / b) + S % b := (Nat.div_add_mod S b).symm
    have h_mod_lt : S % b < b := Nat.mod_lt S hb
    have h_eq : b * A + S = (A + S / b) * b + S % b := by
      calc
        b * A + S = b * A + (b * (S / b) + S % b) := by
          conv =>
            lhs
            rw [hS_eq]
        _ = (A + S / b) * b + S % b := by ring
    rw [h_eq]
    have h_rhs : (A + S / b + 1) * b = (A + S / b) * b + b := by ring
    rw [h_rhs]
    exact Nat.add_lt_add_left h_mod_lt _

/-- If `i < n`, then `n + i < 2 * n`. Useful when `i` indexes the second half
of a length-`2*n` array: positions from `n` to `n + i` are still within bounds. -/
lemma n_plus_i_lt_two_n {n i : Nat} (hi : i < n) : n + i < 2 * n := by
  omega

/-- If `s ≤ n / 2`, then `2 * s ≤ n`. -/
lemma two_mul_le_of_le_half {n s : Nat} (h : s ≤ n / 2) : 2 * s ≤ n := by
  have h_mul : 2 * s ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 h
  have h_div : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  exact Nat.le_trans h_mul h_div

/-- `2*a ≤ b ↔ a ≤ b / 2`. The equivalence between doubling and halving.
This is the bidirectional version of `two_mul_le_of_le_half`. -/
lemma two_mul_le_iff_le_half {a b : Nat} : 2 * a ≤ b ↔ a ≤ b / 2 := by
  constructor
  · intro h
    calc
      a = (2 * a) / 2 := by omega
      _ ≤ b / 2 := Nat.div_le_div_right h
  · intro h
    have h_mul : 2 * a ≤ 2 * (b / 2) := Nat.mul_le_mul_left 2 h
    have h_div : 2 * (b / 2) ≤ b := Nat.mul_div_le b 2
    omega

/-- If `a ≤ b` and `b < a + c`, then `b - a < c`. -/
lemma sub_lt_of_lt_add {a b c : Nat} (hle : a ≤ b) (hlt : b < a + c) : b - a < c := by
  omega

/-- If `0 < a`, then `a - 1 - b < a`. A simple bound on double subtraction:
subtracting 1 then `b` from a positive `a` still leaves a result strictly less than `a`. -/
lemma sub_one_sub_lt_of_pos {a b : Nat} (ha : 0 < a) : a - 1 - b < a := by
  omega

/-- `b - (a + 1) < b - a` when `a < b`. Useful for termination proofs of functions
that decrement an index towards zero (e.g., `size - (pos + 1) < size - pos`).
The intuition: subtracting a larger amount leaves a smaller result. -/
lemma sub_succ_lt_sub_of_lt {a b : Nat} (h : a < b) : b - (a + 1) < b - a := by
  omega

/-- If `a + b ≤ c` and `b` is positive, then `a < c`. Useful for showing that
a start index is strictly within bounds when a non-zero-length window fits.
For example: `pos + k ≤ size` with `0 < k` implies `pos < size`. -/
lemma lt_of_add_pos_and_le {a b c : Nat} (hb : 0 < b) (h : a + b ≤ c) : a < c := by
  omega

/-- If `k ≤ n` and `i < n - k + 1`, then `i + k ≤ n`.
This is useful for bounding subarray indices: `i` is a valid start index
for a length-`k` subarray within a length-`n` array. -/
lemma add_le_of_lt_sub_add_one {n k i : Nat} (hk : k ≤ n) (hi : i < n - k + 1) : i + k ≤ n := by
  omega

/-- Given `p ≤ s`, the condition `i + p ≤ s` is equivalent to `i < (s - p) + 1`.
This is the core identity for sliding-window and subarray problems:
the window fits inside the sequence exactly when the start index
is before the last possible starting position. -/
lemma add_le_iff_lt_sub_add_one {i p s : Nat} (hp : p ≤ s) :
    i + p ≤ s ↔ i < (s - p) + 1 := by
  omega

/-- If `k ≤ n` and `i ∈ Finset.range (n - k + 1)`, then `i + k ≤ n`.
This is the Finset-membership version of `add_le_of_lt_sub_add_one`:
it converts `Finset.range` membership back to the arithmetic inequality. -/
lemma add_le_of_mem_range {i k n : Nat} (hk : k ≤ n) (h : i ∈ Finset.range (n - k + 1)) :
    i + k ≤ n := by
  have hi_lt : i < n - k + 1 := Finset.mem_range.mp h
  have hi_le : i ≤ n - k := Nat.le_of_lt_succ hi_lt
  calc
    i + k ≤ (n - k) + k := Nat.add_le_add_right hi_le k
    _ = n := Nat.sub_add_cancel hk

/-- If `k ≤ n` and `i ∈ List.range (n - k + 1)`, then `i + k ≤ n`.
This is the List-membership version of `add_le_of_lt_sub_add_one`:
it converts `List.range` membership back to the arithmetic inequality. -/
lemma add_le_of_mem_list_range {i k n : Nat} (hk : k ≤ n) (h : i ∈ List.range (n - k + 1)) :
    i + k ≤ n := by
  have hi_lt : i < n - k + 1 := List.mem_range.1 h
  omega

/-- If `a < n`, then `a + 1` lies in the range `[1, n]`. In particular,
`1 ≤ a + 1` (always true for `Nat`) and `a + 1 ≤ n` (the key bound).
Useful for converting a strict upper bound on `a` into an inclusive bound on `a + 1`. -/
lemma add_one_bounds_of_lt {a n : Nat} (h : a < n) : 1 ≤ a + 1 ∧ a + 1 ≤ n := by
  omega

/-- If `1 ≤ k ≤ n`, then `k - 1 < n`.
Useful for converting a 1-indexed inclusive bound `k ≤ n` into a 0-indexed strict bound
for array/list access: `result[k - 1]` is within bounds of a length-`n` list. -/
lemma sub_one_lt_of_one_le_le {n k : Nat} (h₁ : 1 ≤ k) (h₂ : k ≤ n) : k - 1 < n := by
  omega

/--
When `2 ≤ n`, dividing by 2 yields a positive result.
Useful for showing division by 2 preserves nonzeroness.
-/
lemma div_two_pos_of_two_le {n : Nat} (h : 2 ≤ n) : 0 < n / 2 := by
  apply Nat.div_pos <;> omega

/-- If `k ≤ n`, `k ≤ m`, and `res ≤ a ^ k`, then `res ≤ a ^ (min n m)` (for `a > 0`).
This follows from the monotonicity of `a ^ k` in `k` and transitivity. -/
lemma le_pow_min_of_bound {a n m k res : Nat} (ha_pos : 0 < a) (h_le_n : k ≤ n) (h_le_m : k ≤ m)
    (h_res_le : res ≤ a ^ k) : res ≤ a ^ (Nat.min n m) := by
  have h_min_ge_k : k ≤ Nat.min n m := Nat.le_min.mpr ⟨h_le_n, h_le_m⟩
  have h_pow_ge : a ^ k ≤ a ^ (Nat.min n m) := Nat.pow_le_pow_right ha_pos h_min_ge_k
  omega

/--
When `1 < n`, dividing by 2 yields a strictly smaller natural number.
Useful for termination proofs of divide-by-2 recursions.
-/
lemma div_two_lt_self {n : Nat} (hn : 1 < n) : n / 2 < n :=
  Nat.div_lt_self (by omega) (by decide)

/-- When `1 < base` and `n ≠ 0`, integer division by `base` strictly decreases `n`.
Generalizes `div_two_lt_self` to any base > 1. -/
lemma div_lt_self_of_one_lt_base {base n : Nat} (hbase : 1 < base) (hn : n ≠ 0) : n / base < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero hn) hbase

/-- If `2*a < n` and `n` is even, then `a < n/2`. -/
lemma lt_div_two_of_two_mul_lt {a n : Nat} (hdvd : 2 ∣ n) (h : 2*a < n) : a < n/2 := by
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at h ⊢
  have : a < k := by omega
  simpa using this

/-- If `a ≤ 2*n` then `a/2 ≤ n`. -/
lemma div_two_le_of_mul_two_le (a n : Nat) (h : a ≤ 2*n) : a / 2 ≤ n := by
  have h_div : a/2 ≤ (2*n)/2 := Nat.div_le_div_right h
  have h_simp : (2*n)/2 = n := by
    rw [Nat.mul_div_cancel_left n (by decide : 0 < 2)]
  rw [h_simp] at h_div
  exact h_div

/-- Division by two: `(a * 2 + r) / 2 = a` when `r < 2` (i.e., `r = 0` or `r = 1`).
This is a convenient form of `Nat.div_add_mod` specialized to divisor 2. -/
lemma div_two_mul_add_of_lt_two {a r : Nat} (hr : r < 2) : (a * 2 + r) / 2 = a := by
  omega

/-- If `i + 1 < n`, then `i < n - 1` (in Nat, with truncating subtraction).
This is useful when converting between strict index bounds: if index `i + 1` is
within bounds, then index `i` is strictly less than the length minus one. -/
lemma lt_sub_one_of_succ_lt {i n : Nat} (h : i + 1 < n) : i < n - 1 := by
  omega

/-- When `1 < sz`, the conditions `i < sz - 1` and `i + 1 < sz` are equivalent.
This is the bidirectional version of `lt_sub_one_of_succ_lt`. -/
lemma lt_sub_one_iff_succ_lt {i sz : Nat} (hsz : 1 < sz) : i < sz - 1 ↔ i + 1 < sz := by
  omega

/-- If `m ≤ 1`, then `i + 1 < m` is impossible for any `i`.
This is a useful bound-elimination lemma: when a Nat is at most 1,
no index `i` can satisfy `i + 1 < m`. -/
lemma not_succ_lt_of_le_one (i m : Nat) (hm : m ≤ 1) : ¬ (i + 1 < m) := by
  omega

/-- If `n ∣ a` and `a = b * n` and `0 < n`, then `a / n = b`.
This is a convenience wrapper for canceling a known divisor from a division. -/
lemma div_eq_of_dvd_and_eq_mul {a b n : Nat} (hdvd : n ∣ a) (h_eq : a = b * n) (hpos : 0 < n) :
    a / n = b :=
  Nat.eq_of_mul_eq_mul_right hpos (by
    calc
      (a / n) * n = a := Nat.div_mul_cancel hdvd
      _ = b * n := h_eq)

end Nat

namespace Nat

/-! ### Inequality lemmas -/

/-- If `q ≤ k` and `q ≠ k`, then `q ≤ k - 1`.
This is useful when we know a natural number is strictly less than another
and need to bound it by the predecessor. -/
lemma le_of_le_ne {q k : Nat} (hq_le : q ≤ k) (hq_ne : q ≠ k) : q ≤ k - 1 := by
  have hq_lt_k : q < k := Nat.lt_of_le_of_ne hq_le hq_ne
  omega

/-- If `a ≤ b` and `a ≠ b`, then `a + 1 ≤ b`. This is the "strict inequality converted
to a successor bound" version: from `a ≤ b` and `a ≠ b` we deduce `a < b`, then the
strict inequality turns into `a + 1 ≤ b`. Useful when reasoning about integer-indexed
loops and array traversal where positions must advance by at least one. -/
lemma succ_le_of_le_of_ne {a b : Nat} (hle : a ≤ b) (hne : a ≠ b) : a + 1 ≤ b := by
  have hlt : a < b := Nat.lt_of_le_of_ne hle hne
  omega

/-- If `1 ≤ n` then `n ≠ 0`. Useful as a quick bridge from a lower bound to nonzeroness. -/
lemma ne_zero_of_one_le {n : Nat} (h : 1 ≤ n) : n ≠ 0 := by
  omega

/-- If a positive natural number is not equal to 1, it must be greater than 1.
This is the "strict inequality from positivity plus non-one" lemma. -/
lemma ne_one_of_pos {n : Nat} (hne : n ≠ 1) (hpos : 0 < n) : n > 1 := by
  omega

/-- In the context `start ≤ fin`, the upper-bound condition
`n < start + (fin - start + 1)` is equivalent to the simpler `n ≤ fin`.
This is useful for simplifying membership in inclusive ranges. -/
lemma lt_start_add_sub_add_one_iff_le {n start fin : Nat} (h_start_le_fin : start ≤ fin) :
    n < start + (fin - start + 1) ↔ n ≤ fin := by
  constructor
  · omega
  · omega


/-- If `b - a < m` and `a ≤ b`, then `b < m + a`.
This is useful when we have a bound on the difference and need a bound on the sum. -/
lemma sub_lt_imp_add_lt {a b m : Nat} (h_sub_lt : b - a < m) (h_le : a ≤ b) : b < m + a := by
  have h := Nat.add_lt_add_right h_sub_lt a
  rw [Nat.sub_add_cancel h_le] at h
  exact h

/-- If `k` is positive, then `(k - 1) + 1 = k`. This is the "predecessor + 1" identity,
useful when manipulating index arithmetic where `k` is known to be positive. -/
lemma sub_add_one_of_pos {k : Nat} (h : 0 < k) : (k - 1) + 1 = k := by
  omega

/-- If `0 < k` and `k ≤ len`, then `k - 1 < len`. Useful for converting
1-based indexing to 0-based index bounds. -/
lemma sub_one_lt_of_le' {k len : Nat} (h_pos : 0 < k) (h_le : k ≤ len) : k - 1 < len := by
  have hsub : k - 1 < k := Nat.sub_lt h_pos (by decide : 0 < 1)
  omega

/-- If `¬ a < b` and `¬ b < a`, then `a = b`.
This is a convenience lemma combining `Nat.le_of_not_gt` with `Nat.le_antisymm`.
Useful when you have excluded both `a < b` and `b < a` and need equality. -/
lemma eq_of_not_lt_and_not_lt {a b : Nat} (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  Nat.le_antisymm (Nat.le_of_not_gt h2) (Nat.le_of_not_gt h1)

/-- If `n` is positive and `i + n ≤ m`, then `i < m + 1`.
This captures the common pattern: an index `i` plus a positive offset `n` fits within `m`,
so the index itself is strictly less than `m + 1`. Useful for range-bound proofs. -/
lemma lt_succ_of_add_pos_le {m n i : Nat} (hn_pos : 0 < n) (h_bound : i + n ≤ m) : i < m + 1 := by
  have h : i + 1 ≤ i + n := by omega
  have h' : i + 1 ≤ m := Nat.le_trans h h_bound
  omega

/-- If `a ⊓ b = a`, then `a ≤ b`. This is the converse of `Nat.min_eq_left`. -/
lemma le_of_min_eq_left {a b : Nat} (h : a ⊓ b = a) : a ≤ b := by
  calc
    a = a ⊓ b := by symm; exact h
    _ ≤ b := Nat.min_le_right _ _

/-- If `max a b = b`, then `a ≤ b`. This is the converse of `Nat.max_eq_right`.
Useful when the max of two numbers equals the second, deducing the first does not exceed it. -/
lemma le_of_max_eq_right {a b : Nat} (h : max a b = b) : a ≤ b := by
  by_contra! hgt
  have hmax : max a b = a := Nat.max_eq_left (by omega)
  rw [hmax] at h
  omega

/-- The expression `if a > b then a else b` equals `max a b` for natural numbers.
This bridges the if-then-else idiom used in `foldl` max computations with the standard `max` function. -/
theorem ite_gt_eq_max (a b : Nat) : (if a > b then a else b) = max a b := by
  by_cases h : a > b
  · have hle : b ≤ a := Nat.le_of_lt h
    simp [h, hle]
  · have hle : a ≤ b := by omega
    simp [h, hle]

/-- Bound lemma: if `i < n - m + 1`, `1 ≤ m`, and `1 ≤ n`, then `i < n`.
Useful when iterating over a range of length `n - m + 1` and needing
to relate the index back to the full array length. -/
lemma lt_n_of_lt_n_sub_m_succ {i n m : Nat} (h_lt : i < n - m + 1) (hm_pos : 1 ≤ m) (hn_pos : 1 ≤ n) : i < n := by
  by_cases hmn : m ≤ n
  · -- m ≤ n: range is tight, i fits within n
    have hi_le_n_sub_m : i ≤ n - m := Nat.le_of_lt_succ h_lt
    have hi_add_m_le_n : i + m ≤ n := by
      calc
        i + m ≤ (n - m) + m := Nat.add_le_add_right hi_le_n_sub_m m
        _ = n := Nat.sub_add_cancel hmn
    have hi_lt_ipm : i < i + m := by
      have hm_pos' : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 1) hm_pos
      exact Nat.lt_add_of_pos_right hm_pos'
    exact Nat.lt_of_lt_of_le hi_lt_ipm hi_add_m_le_n
  · -- n < m: range collapses to {0}, i=0, and 1≤n gives 0<n
    have h_sub_zero : n - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hmn))
    have hi_lt_one : i < 1 := by simpa [h_sub_zero] using h_lt
    have hi_zero : i = 0 := Nat.lt_one_iff.mp hi_lt_one
    have h0_lt_n : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 1) hn_pos
    simpa [hi_zero] using h0_lt_n

/-- Bound lemma: if `i < n - m + 1` and `m ≤ n`, then `i + m ≤ n`.
Ensures that an `m`-length slice starting at `i` fits within `n`. -/
lemma add_m_le_n_of_lt_n_sub_m_succ {i n m : Nat} (h_lt : i < n - m + 1) (hm_le_n : m ≤ n) : i + m ≤ n := by
  have hi_le_n_sub_m : i ≤ n - m := Nat.le_of_lt_succ h_lt
  calc
    i + m ≤ (n - m) + m := Nat.add_le_add_right hi_le_n_sub_m m
    _ = n := Nat.sub_add_cancel hm_le_n

end Nat



namespace Nat

/-! ### `stepsToZero` — number of steps to reduce a number to zero -/

/--
Number of steps required to reduce a natural number `n` to zero by repeatedly:
- dividing by 2 when `n` is even (and positive),
- subtracting 1 when `n` is odd.

This is the core recurrence from LeetCode 1342 "Number of Steps to Reduce a Number to Zero".
For `n = 0`, returns `0`. For `n > 0`, returns `popCount n + Nat.log2 n`.
-/
def stepsToZero : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      1 + stepsToZero ((n + 1) / 2)
    else
      1 + stepsToZero n
termination_by n => n
decreasing_by
  · apply Nat.div_lt_self (Nat.succ_pos _) (by decide)
  · omega

/-! ### `maxBelow` — max of accumulator and element, bounded above -/

/-- `maxBelow bound acc s` returns `max acc s` if `s ≤ bound`, otherwise `acc`.
This is the fold function for finding the maximum element in a list that is ≤ `bound`. -/
def maxBelow (bound acc s : Nat) : Nat :=
  if s ≤ bound then max acc s else acc

/-- If `acc ≤ bound`, then `maxBelow bound acc s ≤ bound`. -/
lemma maxBelow_le_bound (bound acc s : Nat) (ha : acc ≤ bound) : maxBelow bound acc s ≤ bound := by
  unfold maxBelow; split <;> omega

/-- The accumulator is always ≤ `maxBelow bound acc s`. -/
lemma maxBelow_ge_acc (bound acc s : Nat) : acc ≤ maxBelow bound acc s := by
  unfold maxBelow; split
  · exact Nat.le_max_left _ _
  · exact le_rfl

/-- If `s ≤ bound`, then `s ≤ maxBelow bound acc s`. -/
lemma maxBelow_ge_s (bound s acc : Nat) (hs : s ≤ bound) : s ≤ maxBelow bound acc s := by
  unfold maxBelow; simp [hs]

/-- `maxBelow` returns either the accumulator or the current element. -/
lemma maxBelow_eq_or (bound acc s : Nat) : maxBelow bound acc s = acc ∨ maxBelow bound acc s = s := by
  unfold maxBelow
  split
  · by_cases h : acc ≤ s
    · right; exact Nat.max_eq_right h
    · left; exact Nat.max_eq_left (by omega)
  · left; rfl

/-! ### Pair ordering -/

/-- Lexicographic ordering on `Nat × Nat`: compare by first component, then by second.
Used with `List.Sorted` to verify pairs are sorted. -/
def pair_le (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-! ### Min/max pair equivalence -/

/-- If two pairs of naturals share the same minimum and maximum,
    then the pairs are equal up to order (i.e., either `(a = c ∧ b = d)` or `(a = d ∧ b = c)`). -/
lemma min_max_pair_eq_imp_equiv {a b c d : Nat} (hmin : min a b = min c d) (hmax : max a b = max c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h_cases_ab := Nat.le_total a b
  have h_cases_cd := Nat.le_total c d
  rcases h_cases_ab with (hab | hba)
  · -- a ≤ b: min a b = a, max a b = b
    have ha_min : min a b = a := Nat.min_eq_left hab
    have hb_max : max a b = b := Nat.max_eq_right hab
    rw [ha_min] at hmin
    rw [hb_max] at hmax
    rcases h_cases_cd with (hcd | hdc)
    · -- c ≤ d: min c d = c, max c d = d
      have hc_min : min c d = c := Nat.min_eq_left hcd
      have hd_max : max c d = d := Nat.max_eq_right hcd
      rw [hc_min] at hmin
      rw [hd_max] at hmax
      left; exact ⟨hmin, hmax⟩
    · -- d ≤ c: min c d = d, max c d = c
      have hd_min : min c d = d := Nat.min_eq_right hdc
      have hc_max : max c d = c := Nat.max_eq_left hdc
      rw [hd_min] at hmin
      rw [hc_max] at hmax
      right; exact ⟨hmin, hmax⟩
  · -- b ≤ a: min a b = b, max a b = a
    have hb_min : min a b = b := Nat.min_eq_right hba
    have ha_max : max a b = a := Nat.max_eq_left hba
    rw [hb_min] at hmin
    rw [ha_max] at hmax
    rcases h_cases_cd with (hcd | hdc)
    · -- c ≤ d: min c d = c, max c d = d
      have hc_min : min c d = c := Nat.min_eq_left hcd
      have hd_max : max c d = d := Nat.max_eq_right hcd
      rw [hc_min] at hmin
      rw [hd_max] at hmax
      right; exact ⟨hmax, hmin⟩
    · -- d ≤ c: min c d = d, max c d = c
      have hd_min : min c d = d := Nat.min_eq_right hdc
      have hc_max : max c d = c := Nat.max_eq_left hdc
      rw [hd_min] at hmin
      rw [hc_max] at hmax
      left; exact ⟨hmax, hmin⟩

end Nat


namespace Nat


/-! ### Minimum of three numbers -/

/-- Minimum of three natural numbers. -/
def min3 (a b c : Nat) : Nat := Nat.min a (Nat.min b c)

lemma min3_zero_left (b c : Nat) : min3 0 b c = 0 := by
  simp [min3]

/-! ### Maximum of three numbers -/

/-- Maximum of three natural numbers. This is the dual of `min3`. -/
def max3 (a b c : Nat) : Nat := Nat.max a (Nat.max b c)

lemma max3_zero_right (a b : Nat) : max3 a b 0 = max a b := by
  simp [max3]



/-! ### Three-way comparison with custom labels -/

/-- Based on comparing two natural numbers `a` and `b`, return one of three labels:
`gtLabel` if `a > b`, `ltLabel` if `b > a`, or `eqLabel` if `a = b`.

This generalizes `compareNat` (which returns fixed numeric codes 1/2/0)
by allowing arbitrary return types `α`. -/
def byComparison {α : Type} (a b : Nat) (gtLabel ltLabel eqLabel : α) : α :=
  if a > b then gtLabel
  else if b > a then ltLabel
  else eqLabel

/-- Specification for `byComparison`: the result equals `gtLabel` when `a > b`,
`ltLabel` when `b > a`, and `eqLabel` when `a = b`. -/
lemma byComparison_spec {α : Type} (a b : Nat) (gtLabel ltLabel eqLabel : α) :
    (byComparison a b gtLabel ltLabel eqLabel = gtLabel ∧ a > b) ∨
    (byComparison a b gtLabel ltLabel eqLabel = ltLabel ∧ b > a) ∨
    (byComparison a b gtLabel ltLabel eqLabel = eqLabel ∧ a = b) := by
  unfold byComparison
  by_cases h : a > b
  · simp [h]
  · by_cases h' : b > a
    · simp [h, h']
    · have heq : a = b := _root_.eq_of_not_gt_and_not_gt h h'
      simp [h, h', heq]

/-! ### Three-way comparison (numeric codes) -/

/-- Three-way comparison of two natural numbers:
returns 1 if `a > b`, 2 if `b > a`, 0 if `a = b`.
Defined as a specialization of `byComparison`. -/
def compareNat (a b : Nat) : Nat :=
  byComparison a b 1 2 0

/-- Specification for `compareNat`: its return value uniquely encodes
which of `a`, `b` is larger, or whether they are equal. -/
lemma compareNat_spec (a b : Nat) :
    (compareNat a b = 1 ∧ a > b) ∨ (compareNat a b = 2 ∧ b > a) ∨ (compareNat a b = 0 ∧ a = b) := by
  unfold compareNat
  rcases byComparison_spec a b 1 2 0 with (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ### Bool-Prop bridge for comparisons -/

/-- Relates the boolean `a ≥ n` to the propositional `n ≤ a` for natural numbers.
    Useful when a `Bool` decision is lifted to a `Prop` equivalence. -/
lemma bool_ge_iff_le (a n : Nat) : (((a ≥ n : Bool) = true) ↔ n ≤ a) := by
  simp

/-! ### Argmax over index range with tiebreaking -/

/-- Iterate through indices from `cur` to `len-1` to find the index that maximizes `val` and,
    among ties, minimizes `tiebreak` (lexicographic order: larger `val` then smaller `tiebreak`).
    `cur`: current index being examined
    `bestIdx`: index of the best element found so far
    `maxVal`: maximum `val` found so far
    Returns the index of the best element. -/
def findMaxIndexBy (val tiebreak : Nat → Nat) (len cur bestIdx maxVal : Nat) : Nat :=
  if h : cur < len then
    let v := val cur
    if v > maxVal ∨ (v = maxVal ∧ tiebreak cur < tiebreak bestIdx) then
      findMaxIndexBy val tiebreak len (cur + 1) cur v
    else
      findMaxIndexBy val tiebreak len (cur + 1) bestIdx maxVal
  else
    bestIdx
termination_by len - cur

/-- Specification lemma for `findMaxIndexBy`: the returned index is within bounds, has maximal
    `val` among all indices, and satisfies the tie-breaking condition
    (smallest `tiebreak` among indices with maximal `val`). -/
lemma findMaxIndexBy_spec (val tiebreak : Nat → Nat) (len cur bestIdx maxVal : Nat)
    (h_bestIdx_lt_len : bestIdx < len)
    (h_bestVal_eq : val bestIdx = maxVal)
    (h_opt : ∀ j, j < cur → val j ≤ maxVal)
    (h_tie : ∀ j, j < cur → val j = maxVal → tiebreak bestIdx ≤ tiebreak j) :
    let bestIdx' := findMaxIndexBy val tiebreak len cur bestIdx maxVal
    bestIdx' < len ∧
    (∀ j, j < len → val j ≤ val bestIdx') ∧
    (∀ j, j < len → val j = val bestIdx' → tiebreak bestIdx' ≤ tiebreak j) := by
  let P (k : Nat) : Prop :=
    ∀ (c b m : Nat),
      len - c = k →
      b < len →
      val b = m →
      (∀ j, j < c → val j ≤ m) →
      (∀ j, j < c → val j = m → tiebreak b ≤ tiebreak j) →
      (findMaxIndexBy val tiebreak len c b m < len ∧
       (∀ j, j < len → val j ≤ val (findMaxIndexBy val tiebreak len c b m)) ∧
       (∀ j, j < len → val j = val (findMaxIndexBy val tiebreak len c b m) →
         tiebreak (findMaxIndexBy val tiebreak len c b m) ≤ tiebreak j))
  have hP : ∀ k, P k := by
    intro k
    induction' k with k IH
    · -- Base case: k = 0, so len - c = 0, hence c ≥ len
      intro c b m h_eq h_lt_len h_val_eq h_opt' h_tie'
      have hc_ge : len ≤ c := by
        have : len - c = 0 := h_eq
        omega
      unfold findMaxIndexBy
      by_cases hlt : c < len
      · omega
      · simp [hlt]
        refine ⟨h_lt_len, ?_, ?_⟩
        · intro j hj
          have hj_lt_c : j < c := lt_of_lt_of_le hj hc_ge
          simpa [h_val_eq] using h_opt' j hj_lt_c
        · intro j hj h_eq_val_j
          have hj_lt_c : j < c := lt_of_lt_of_le hj hc_ge
          have h_eq_val_j' : val j = m := by
            simpa [h_val_eq] using h_eq_val_j
          simpa using h_tie' j hj_lt_c h_eq_val_j'
    · -- Inductive case: k = k.succ, so c < len
      intro c b m h_eq h_lt_len h_val_eq h_opt' h_tie'
      have hc_lt : c < len := by
        by_contra! hge
        have : len - c = 0 := Nat.sub_eq_zero_of_le hge
        omega
      unfold findMaxIndexBy
      split
      · -- True branch: h : c < len
        simp
        by_cases h_upd : val c > m ∨ (val c = m ∧ tiebreak c < tiebreak b)
        · -- Update case: c becomes the new best
          have h_new_opt : ∀ j, j < c + 1 → val j ≤ val c := by
            intro j hj
            have h_cases : j < c ∨ j = c := by omega
            rcases h_cases with (h_lt | rfl)
            · have h_le : val j ≤ m := h_opt' j h_lt
              rcases h_upd with (h_gt | ⟨h_eq_val, _⟩)
              · omega
              · rw [h_eq_val]; exact h_le
            · rfl
          have h_new_tie : ∀ j, j < c + 1 → val j = val c → tiebreak c ≤ tiebreak j := by
            intro j hj h_eq_val_j
            have h_cases : j < c ∨ j = c := by omega
            rcases h_cases with (h_lt | rfl)
            · rcases h_upd with (h_gt | ⟨h_eq_val_max, h_lt_tb⟩)
              · have h_le : val j ≤ m := h_opt' j h_lt
                omega
              · have h_eq_max : val j = m := by
                  rw [← h_eq_val_max, h_eq_val_j]
                have h_tie_prev : tiebreak b ≤ tiebreak j := h_tie' j h_lt h_eq_max
                have h_strict : tiebreak c < tiebreak j :=
                  lt_of_lt_of_le h_lt_tb h_tie_prev
                exact Nat.le_of_lt h_strict
            · rfl
          have h_measure : len - (c + 1) = k := by omega
          have h_rec := IH (c + 1) c (val c) h_measure hc_lt rfl h_new_opt h_new_tie
          rw [if_pos h_upd]
          simpa using h_rec
        · -- No update case: keep current best
          have h_not_gt : ¬ (val c > m) := by
            intro h; apply h_upd; exact Or.inl h
          have h_curVal_le : val c ≤ m := Nat.le_of_not_gt h_not_gt
          have h_curVal_eq_implies : val c = m → tiebreak b ≤ tiebreak c := by
            intro heq
            have h_not_lt : ¬ (tiebreak c < tiebreak b) := by
              intro hlt; apply h_upd; exact Or.inr ⟨heq, hlt⟩
            exact Nat.le_of_not_gt h_not_lt
          have h_new_opt : ∀ j, j < c + 1 → val j ≤ m := by
            intro j hj
            have h_cases : j < c ∨ j = c := by omega
            rcases h_cases with (h_lt | rfl)
            · exact h_opt' j h_lt
            · exact h_curVal_le
          have h_new_tie : ∀ j, j < c + 1 → val j = m → tiebreak b ≤ tiebreak j := by
            intro j hj h_eq_val_j
            have h_cases : j < c ∨ j = c := by omega
            rcases h_cases with (h_lt | h_eq_jc)
            · exact h_tie' j h_lt h_eq_val_j
            · have h_curVal_eq_m : val c = m := by
                simpa [h_eq_jc] using h_eq_val_j
              rw [h_eq_jc]
              exact h_curVal_eq_implies h_curVal_eq_m
          have h_measure : len - (c + 1) = k := by omega
          have h_rec := IH (c + 1) b m h_measure h_lt_len h_val_eq h_new_opt h_new_tie
          have h_not_upd : ¬ (val c > m ∨ (val c = m ∧ tiebreak c < tiebreak b)) := h_upd
          rw [if_neg h_not_upd]
          simpa using h_rec
      · -- False branch: h : ¬ c < len, contradicts hc_lt
        rename_i h
        exfalso; exact h hc_lt
  have h_initial : len - cur = len - cur := rfl
  exact hP (len - cur) cur bestIdx maxVal h_initial h_bestIdx_lt_len h_bestVal_eq h_opt h_tie



/-! ### `Nat.ble` transitivity and totality

These lemmas provide transitivity and totality of the `Nat.ble` boolean relation,
which is the `Bool` counterpart of `Nat.le`. They are required by `List.sorted_mergeSort`
when using `Nat.ble` directly (rather than `decide (· ≤ ·)`) as a comparator. -/

/-- Transitivity of `Nat.ble = true`, i.e. of the `≤` relation. -/
lemma ble_trans (a b c : Nat) (h1 : a.ble b = true) (h2 : b.ble c = true) : a.ble c = true := by
  rw [Nat.ble_eq] at h1 h2 ⊢
  exact Nat.le_trans h1 h2

/-- Totality of `Nat.ble`: `(a.ble b || b.ble a) = true` for all `a, b`. -/
lemma ble_total (a b : Nat) : (a.ble b || b.ble a) = true := by
  have h := le_total a b
  rcases h with (h | h)
  · have ha : a.ble b = true := by rw [Nat.ble_eq]; exact h
    simp [ha]
  · have hb : b.ble a = true := by rw [Nat.ble_eq]; exact h
    simp [hb]


end Nat

namespace Nat

/-!
# Minimum over a range of natural numbers

This module provides `foldMinIter`, a general-purpose function that iterates
over `f 0, f 1, …, f (n-1)` keeping the minimum. It takes a function
`f : Nat → α` where `α` has a `LinearOrder`, an upper bound `n : Nat`, and an
initial value `init : α`, returning the minimum of `init` and all `f k` for
`k < n`.

This is useful for problems that need to find the minimum value of a function
over a prefix of natural numbers, such as "smallest rotation of a string" or
"minimum prefix sum".
-/

/-- Iteratively combines `f 0, f 1, …, f (n-1)` by keeping the smaller one,
starting from `init`. At step `k`, replaces the accumulator with `f k` if `f k` is
strictly smaller. Returns the minimum among `{init} ∪ {f k | k < n}`. -/
def foldMinIter {α : Type} [LinearOrder α] (f : Nat → α) (n : Nat) (init : α) : α :=
  Nat.rec (motive := fun _ => α) init (fun k ih => if f k < ih then f k else ih) n

/-- The main invariant of `foldMinIter`: for any `n`, the result equals some `f i`
(with `i` suitably bounded) and is ≤ all `f j` for `j < n`.
The hypothesis `hinit` ensures the initial value is `f 0`. -/
lemma foldMinIter_invariant {α : Type} [LinearOrder α]
    (f : Nat → α) (n : Nat) (init : α) (hinit : init = f 0) :
    ∃ i : Nat, (i < n ∨ (n = 0 ∧ i = 0)) ∧ foldMinIter f n init = f i ∧
    (∀ j, j < n → foldMinIter f n init ≤ f j) := by
  induction n with
  | zero =>
    refine ⟨0, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
    · simp [foldMinIter, hinit]
    · intro j hj
      exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    obtain ⟨i, hi_range, hRm_eq, hRm_min⟩ := ih
    have hR_succ : foldMinIter f (m+1) init =
        if f m < foldMinIter f m init then f m else foldMinIter f m init := by
      simp [foldMinIter]
    rw [hR_succ]
    by_cases hlt : f m < foldMinIter f m init
    · rw [if_pos hlt]
      refine ⟨m, Or.inl (Nat.lt_succ_self m), rfl, ?_⟩
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
      · have hRm_le : foldMinIter f m init ≤ f j := hRm_min j hjlt
        exact le_of_lt (lt_of_lt_of_le hlt hRm_le)
      · subst hjeq; exact le_refl _
    · rw [if_neg hlt]
      refine ⟨i, ?_, hRm_eq, ?_⟩
      · rcases hi_range with hi1 | ⟨hm0, hi0⟩
        · exact Or.inl (Nat.lt_succ_of_lt hi1)
        · subst hm0; subst hi0
          exact Or.inl (Nat.zero_lt_succ 0)
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
        · exact hRm_min j hjlt
        · subst hjeq
          exact not_lt.mp hlt

end Nat

namespace Nat

/-! ### Nat cast to Int -/

/-- No natural number cast to `Int` can equal `-1`. -/
lemma natCast_ne_neg_one (n : Nat) : (n : Int) ≠ (-1 : Int) := by
  intro h
  have hn_nonneg : (0 : Int) ≤ (n : Int) := Nat.cast_nonneg _
  rw [h] at hn_nonneg
  linarith

/-! ### Vacuous range lemmas -/

/-- The statement `∀ m : ℕ, m < 0 → P m` holds vacuously for any predicate `P`. -/
lemma forall_lt_zero (P : Nat → Prop) : (∀ m : Nat, m < 0 → P m) :=
  fun m hm => absurd hm (Nat.not_lt_zero m)

/-! ### Existential quantifier simplification for `Nat` -/

/-- Since every natural number is nonnegative, `(∃ j, 0 ≤ j ∧ P j) ↔ (∃ j, P j)`. -/
lemma exists_nonneg_iff {P : Nat → Prop} : (∃ j, 0 ≤ j ∧ P j) ↔ (∃ j, P j) := by
  constructor
  · rintro ⟨j, _, h⟩; exact ⟨j, h⟩
  · rintro ⟨j, h⟩; exact ⟨j, Nat.zero_le j, h⟩

end Nat


namespace Nat


/-! ### Powers of a base -/

/-- Boolean test: is `n` a power of `base` (i.e., `n = base ^ k` for some `k`)?
Returns `false` for `base ≤ 1` unless `n = 1` (since `1 = b^0` for any `b`).
The recursive case requires `base > 1` for termination. -/
def isPowerOfBool (base : Nat) (n : Nat) : Bool :=
  if n = 0 then false
  else if n = 1 then true
  else if base ≤ 1 then false
  else if n % base = 0 then isPowerOfBool base (n / base)
  else false
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-! ### Divisibility helper -/

/-- From `n % d = 0`, infer `n = d * (n / d)`. A useful identity for divisibility reasoning. -/
lemma eq_mul_div_of_mod_eq_zero {n d : Nat} (hmod : n % d = 0) : n = d * (n / d) := by
  have h := Nat.div_add_mod n d
  rw [hmod, add_zero] at h
  exact h.symm

/-- If `d ∣ n`, the quotient `n / d` is less than 2, and both `n` and `d` are positive,
then `d = n`. This is useful for reasoning about when a divisor must be the number
itself (e.g., in prime factorization when `n / minFac n < 2`, meaning `n` is prime). -/
lemma eq_of_div_lt_two {n d : Nat} (hdvd : d ∣ n) (hdiv_lt : n / d < 2)
    (hn_pos : 0 < n) (hd_pos : 0 < d) : d = n := by
  have h_mul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have h_val : n / d = 1 := by
    have hle : n / d ≤ 1 := by omega
    have hd_le_n : d ≤ n := Nat.le_of_dvd hn_pos hdvd
    have hpos' : 0 < n / d := Nat.div_pos hd_le_n hd_pos
    omega
  rw [h_val] at h_mul
  omega

/-! ### Power-of-base theorems -/

/-- For `base > 1`, `base ^ k` passes the `isPowerOfBool` test. -/
lemma isPowerOfBool_true_of_pow (base k : Nat) (hbase : 1 < base) : isPowerOfBool base (base ^ k) = true := by
  induction' k with k ih
  · rw [Nat.pow_zero, isPowerOfBool]; simp
  · rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : base * base ^ k ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero k (by omega))
    have h_not_base_le_one : ¬ base ≤ 1 := by omega
    have hmod0 : (base * base ^ k) % base = 0 := by rw [Nat.mul_mod_right]
    have hdiv_eq : (base * base ^ k) / base = base ^ k := by
      rw [Nat.mul_div_right _ (by omega : 0 < base)]
    have hn1 : base * base ^ k ≠ 1 := by
      have hp_pos : 0 < base ^ k := pow_pos (by omega) k
      have hp_le : 1 ≤ base ^ k := by omega
      have hb2 : 2 ≤ base := by omega
      have hprod : 2 ≤ base * base ^ k :=
        calc
          2 = 2 * 1 := by simp
          _ ≤ base * base ^ k := Nat.mul_le_mul hb2 hp_le
      omega
    rw [isPowerOfBool]
    simp [hpos, hn1, h_not_base_le_one, hmod0, hdiv_eq, ih]

/-- If `isPowerOfBool base n = true` (with `base > 1`), then `n` is truly a power of `base`.
The proof uses strong induction on `n`. -/
lemma isPowerOf_of_isPowerOfBool (base n : Nat) (hbase : 1 < base) (h : isPowerOfBool base n = true) :
    ∃ k : Nat, base ^ k = n := by
  induction' n using Nat.strong_induction_on with n ih
  rw [isPowerOfBool] at h
  split at h
  · simp at h
  · next h0 =>
    split at h
    · next hn1 =>
      rw [hn1]
      exact ⟨0, by simp⟩
    · next h1 =>
      split at h
      · simp at h
      · next h_not_base_le_one =>
        split at h
        · next hmod =>
          have hnpos : 0 < n := Nat.pos_of_ne_zero h0
          have hn_div_lt : n / base < n := Nat.div_lt_self hnpos hbase
          have ih_div := ih (n / base) hn_div_lt h
          rcases ih_div with ⟨k, hk⟩
          have hn_eq : n = base * (n / base) := eq_mul_div_of_mod_eq_zero hmod
          rw [hn_eq, ← hk]
          refine ⟨k + 1, ?_⟩
          rw [Nat.pow_succ, Nat.mul_comm]
        · simp at h

/-- `isPowerOfBool base n = true ↔ ∃ k, n = base ^ k`, for `base > 1`.
Combines `isPowerOfBool_true_of_pow` (reverse direction) and `isPowerOf_of_isPowerOfBool` (forward direction). -/
lemma isPowerOfBool_spec (base n : Nat) (hbase : 1 < base) :
    isPowerOfBool base n = true ↔ ∃ k : Nat, base ^ k = n := by
  constructor
  · exact isPowerOf_of_isPowerOfBool base n hbase
  · intro h
    rcases h with ⟨k, hk⟩
    rw [← hk]
    exact isPowerOfBool_true_of_pow base k hbase

/-- If `a ≥ 2`, `a ^ i ≤ bound`, and `bound < 2 ^ k`, then `i < k`.
This is useful for bounding exponents when the base is at least 2
and a threshold of the form `2 ^ k` is known. -/
lemma exponent_lt_of_pow_le_lt_two_pow {a i bound k : Nat}
    (ha : 2 ≤ a) (hpow : a ^ i ≤ bound) (hbound : bound < 2 ^ k) : i < k := by
  by_contra! h
  have hk_le_i : k ≤ i := by omega
  have h2k_le_2i : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hk_le_i
  have h2i_le_ai : 2 ^ i ≤ a ^ i := Nat.pow_le_pow_left ha i
  have h2k_le_ai : 2 ^ k ≤ a ^ i := Nat.le_trans h2k_le_2i h2i_le_ai
  omega

/-- If `a < 2 ^ n` and `n ≤ m`, then `a < 2 ^ m`. Transitivity of `<` through `Nat.pow_le_pow_right`. -/
lemma lt_two_pow_of_lt_two_pow {a n m : Nat} (ha : a < 2 ^ n) (hnm : n ≤ m) : a < 2 ^ m :=
  lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hnm)


end Nat

namespace Nat


/-! ### Safe division -/

/-- Safe natural number division: returns 0 when the divisor is 0.
Otherwise returns `total / count` as usual. Useful when the divisor
may be zero in specifications, avoiding division-by-zero errors. -/
def safeDiv (divisor numerator : Nat) : Nat :=
  if divisor = 0 then 0 else numerator / divisor

/-- Safe division on naturals returning a `String`: returns `zeroMsg` if the divisor is zero,
otherwise returns the string representation of the quotient.
This is the display-oriented counterpart of `Nat.safeDiv` (which returns `Nat` with `0` as default). -/
def safeDivStr (zeroMsg : String) (a b : Nat) : String :=
  if b = 0 then zeroMsg else toString (a / b)

/-- If the divisor is zero, `safeDivStr` returns the error message. -/
lemma safeDivStr_eq_of_zero (zeroMsg : String) (a b : Nat) (h : b = 0) : safeDivStr zeroMsg a b = zeroMsg := by
  unfold safeDivStr; simp [h]

/-- If the divisor is nonzero, `safeDivStr` returns the string representation of the quotient. -/
lemma safeDivStr_eq_of_ne_zero (zeroMsg : String) (a b : Nat) (h : b ≠ 0) : safeDivStr zeroMsg a b = toString (a / b) := by
  unfold safeDivStr; simp [h]


/-! ### Ceiling division -/

/-- Ceiling division of natural numbers: `roundUpDiv a d = ⌈a / d⌉`.
Equivalent to `(a + d - 1) / d` when `d > 0`. -/
def roundUpDiv (a d : Nat) : Nat :=
  (a + d - 1) / d

/-- Ceiling division by 2: `⌈n/2⌉` computed as `(n + 1) / 2`.
This is a specialization of `roundUpDiv n 2` but uses the simpler formula
`(n + 1) / 2` instead of `(n + 2 - 1) / 2`. -/
def ceilDiv2 (n : Nat) : Nat := (n + 1) / 2

/-- If `a ≤ d` and `0 < d`, then the ceiling division of `a` by `d` is at most `1`. -/
lemma roundUpDiv_le_one_of_le (a d : Nat) (hd : 0 < d) (hle : a ≤ d) : roundUpDiv a d ≤ 1 := by
  unfold roundUpDiv
  rw [Nat.div_le_iff_le_mul hd]
  omega

/-- `roundUpDiv n d ≤ k ↔ n ≤ k * d`, for `0 < d`.
This is the fundamental equivalence linking ceiling division to multiplication. -/
lemma roundUpDiv_le_iff (n d k : Nat) (hd : 0 < d) : roundUpDiv n d ≤ k ↔ n ≤ k * d := by
  unfold roundUpDiv
  rw [Nat.div_le_iff_le_mul hd (x := n + d - 1) (y := k)]
  constructor
  · omega
  · omega

/-- `(h + 1) / 2 ≤ k ↔ h ≤ 2 * k`. The ceiling division by 2 is bounded by `k`
iff the original number `h` is bounded by `2 * k`.
This is the special case `d = 2` of `roundUpDiv_le_iff`. -/
lemma ceilDiv2_le_iff (h k : Nat) : ceilDiv2 h ≤ k ↔ h ≤ 2 * k := by
  rw [ceilDiv2]
  have hpos : 0 < 2 := by decide
  rw [Nat.div_le_iff_le_mul hpos]
  omega

/-- `k < roundUpDiv n d ↔ k * d < n`, for `0 < d`.
This is the strict counterpart of `roundUpDiv_le_iff`. -/
lemma roundUpDiv_lt_iff (n d k : Nat) (hd : 0 < d) : k < roundUpDiv n d ↔ k * d < n := by
  unfold roundUpDiv
  have h := Nat.div_le_iff_le_mul hd (x := n + d - 1) (y := k)
  constructor
  · intro hlt
    have hnotle : ¬ (n + d - 1) / d ≤ k := Nat.not_le_of_lt hlt
    rw [h] at hnotle
    omega
  · intro hlt
    have hnotle : ¬ n + d - 1 ≤ k * d + d - 1 := by omega
    rw [← h] at hnotle
    exact Nat.lt_of_not_ge hnotle

/-- If `0 < n ≤ p` and `0 < p`, then `(n + p - 1) / p = 1`.
That is, the ceiling division of `n` by `p` is exactly `1`. -/
theorem ceil_div_eq_one (n p : Nat) (hn : 0 < n) (hp : 0 < p) (hnp : n ≤ p) : (n + p - 1) / p = 1 := by
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

/-- Ceil division identity: `(a + b - 1) / b = a / b + (if a % b = 0 then 0 else 1)` for `b > 0`.
This relates the standard ceil-division formula to the floor division plus a correction term. -/
lemma ceil_div_eq (a b : Nat) (hb : b > 0) :
    (a + b - 1) / b = a / b + (if a % b = 0 then 0 else 1) := by
  have hdivmod := Nat.div_add_mod a b
  by_cases hmod : a % b = 0
  · simp [hmod]
    apply Nat.div_eq_of_lt_le
    · calc
        (a / b) * b = b * (a / b) := mul_comm _ _
        _ ≤ a + b - 1 := by omega
    · calc
        a + b - 1 < a + b := by omega
        _ = b * (a / b) + b := by
          rw [hmod] at hdivmod
          omega
        _ = ((a / b) + 1) * b := by ring
  · have hmod_pos : 0 < a % b := Nat.pos_of_ne_zero hmod
    simp [hmod]
    apply Nat.div_eq_of_lt_le
    · calc
        (a / b + 1) * b = ((a / b) * b) + b := by ring
        _ = b * (a / b) + b := by ring
        _ ≤ a + b - 1 := by omega
    · calc
        a + b - 1 < a + b := by omega
        _ = b * (a / b) + a % b + b := by omega
        _ < b * (a / b) + b + b := by
          have hmod_lt : a % b < b := Nat.mod_lt a hb
          omega
        _ = ((a / b) + 2) * b := by ring
        _ = ((a / b) + 1 + 1) * b := by ring

/-- If `n + d - 1 < k * d` and `d > 0`, then `roundUpDiv n d < k`.
This is a direct unfolding of `roundUpDiv` using `Nat.div_lt_iff_lt_mul`. -/
lemma roundUpDiv_lt_of_lt_mul (n d k : Nat) (hd : 0 < d) (h : n + d - 1 < k * d) :
    roundUpDiv n d < k := by
  unfold roundUpDiv
  rw [Nat.div_lt_iff_lt_mul hd]
  exact h

/-- Ceiling division `roundUpDiv a b` is positive when `a ≥ 1` and `b > 0`. -/
lemma roundUpDiv_pos (a b : Nat) (ha : 1 ≤ a) (hb : 0 < b) : 0 < roundUpDiv a b := by
  unfold roundUpDiv
  exact Nat.div_pos (by omega) hb

/-- If `a % b ≠ 0` and `b > 0`, then `roundUpDiv a b = a / b + 1`.
This is the case when the division has a non-zero remainder, so the ceiling is one
more than the floor. This is a corollary of `ceil_div_eq`. -/
lemma roundUpDiv_eq_succ_div_of_mod_ne_zero (a b : Nat) (hb : 0 < b) (hmod : a % b ≠ 0) :
    roundUpDiv a b = a / b + 1 := by
  unfold roundUpDiv
  rw [ceil_div_eq a b hb]
  simp [hmod]

/-! ### Rounded division (round-to-nearest) -/

/-- Compute `(a * k) / b`, rounding to the nearest integer (ties round up).
    Returns 0 when `b = 0`.
    This is the standard technique for fixed-point arithmetic:
    multiply first by the scale factor `k`, then divide with rounding.
    Example: `Nat.mulDivRound 7 100 3 = 233` (i.e., `7/3 * 100 ≈ 233.33`, rounded to 233). -/
def mulDivRound (a k b : Nat) : Nat :=
  if b = 0 then 0 else (a * k + b / 2) / b


theorem mulDivRound_zero_denom (a k : Nat) : mulDivRound a k 0 = 0 := by
  simp [mulDivRound]

theorem mulDivRound_zero_left (k b : Nat) : mulDivRound 0 k b = 0 := by
  unfold mulDivRound
  split
  · rfl
  · have hpos : 0 < b := Nat.pos_of_ne_zero ‹_›
    have hcalc : 0 * k + b / 2 = b / 2 := by simp
    rw [hcalc]
    apply Nat.div_eq_of_lt
    exact Nat.div_lt_self hpos (by decide)

theorem mulDivRound_eq_zero_of_lt {a k b : Nat} (h : a * k < b / 2) (hb : b ≠ 0) :
    mulDivRound a k b = 0 := by
  rw [mulDivRound, if_neg hb]
  apply Nat.div_eq_of_lt
  have hsum : a * k + b / 2 < b / 2 + b / 2 := Nat.add_lt_add_right h (b / 2)
  have hbound : b / 2 + b / 2 ≤ b := by
    have := Nat.div_add_mod b 2
    omega
  omega

/-! ### Division / modulo inequalities -/

/-- If `n < a * b` and `0 < b`, then `n / b < a`.
    A convenient form of the forward direction of `Nat.div_lt_iff_lt_mul`. -/
theorem div_lt_of_lt_mul' {n a b : Nat} (hn : n < a * b) (hb : 0 < b) : n / b < a :=
  (Nat.div_lt_iff_lt_mul hb).mpr hn

/-- Bound for the middle component after a two-level decomposition:
    `(n % (a*b)) / b < a` for positive `a`, `b`. -/
theorem div_mod_lt_of_pos {n a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (n % (a * b)) / b < a := by
  have hmod : n % (a * b) < a * b := Nat.mod_lt n (mul_pos ha hb)
  exact div_lt_of_lt_mul' hmod hb

/-- If `a ≤ b`, then `(c * a) / d ≤ (c * b) / d` for any naturals `c`, `d`.
Useful for bounding scaled quantities after integer division. -/
lemma mul_div_le_mul_div_left {a b c d : Nat} (h : a ≤ b) : (c * a) / d ≤ (c * b) / d := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_left c h

/-- `(a * b) / a ≤ b` for natural numbers.
This is the inequality version of `Nat.mul_div_cancel_left`, which requires `a > 0`.
For `a = 0`, both sides are `0 ≤ b` by the reduction `0 / 0 = 0`. -/

lemma mul_div_self_le (a b : Nat) : (a * b) / a ≤ b := by
  by_cases ha : a = 0
  · subst ha; simp
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    have h_eq : (a * b) / a = b := by
      rw [Nat.mul_div_cancel_left b ha_pos]
    rw [h_eq]


end Nat

namespace Nat

/-! ### Ceiling half -/

/-- `ceilHalf n` computes `⌈n/2⌉`, i.e., `(n + 1) / 2`.
For example: `ceilHalf 0 = 0`, `ceilHalf 1 = 1`, `ceilHalf 2 = 1`, `ceilHalf 3 = 2`. -/
def ceilHalf (n : Nat) : Nat := (n + 1) / 2


lemma ceilHalf_zero : ceilHalf 0 = 0 := rfl


lemma ceilHalf_one : ceilHalf 1 = 1 := by
  unfold ceilHalf; decide

lemma ceilHalf_two : ceilHalf 2 = 1 := by
  unfold ceilHalf; decide

lemma ceilHalf_add_ceilHalf_ge (n : Nat) : ceilHalf n + ceilHalf n ≥ n := by
  unfold ceilHalf
  have h : (n + 1) / 2 + (n + 1) / 2 ≥ n := by
    omega
  exact h

lemma ceilHalf_le_self (n : Nat) (hn : 0 < n) : ceilHalf n ≤ n := by
  unfold ceilHalf
  have h : (n + 1) / 2 ≤ n := by omega
  exact h

lemma ceilHalf_lt_self_of_one_lt {n : Nat} (hn : 1 < n) : ceilHalf n < n := by
  unfold ceilHalf
  have h : (n + 1) / 2 < n := by omega
  exact h

lemma two_mul_ceilHalf_ge (n : Nat) : 2 * ceilHalf n ≥ n := by
  unfold ceilHalf
  omega

end Nat
