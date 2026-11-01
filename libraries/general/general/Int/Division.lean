import Mathlib
import general.Int.Core
import general.Nat.NumberTheory

/-! ### Generic safe division (String-returning)

The generic `safeDivResult` returns a user-supplied error message when the divisor
is zero, and `toString (a / b)` otherwise. It works for any type with `Div`,
`DecidableEq`, `Zero`, and `ToString`. For the `Int`-specialized version, see
`Int.safeDivStr`. -/

/-- Safe division result formatted as a string: returns `errMsg` if `b = 0`,
otherwise returns `toString (a / b)`. -/
def safeDivResult [Div α] [DecidableEq α] [Zero α] [ToString α] (a b : α) (errMsg : String) : String :=
  if _ : b = (0 : α) then errMsg else toString (a / b)

/--
Characterizes the result of `safeDivResult`: either the divisor equals zero and the result
is the error message, or the divisor is nonzero and the result is `toString (a / b)`.
-/
lemma safeDivResult_spec {α : Type} [Div α] [DecidableEq α] [Zero α] [ToString α]
    (a b : α) (err : String) :
    (b = (0 : α) ∧ safeDivResult a b err = err) ∨
    (b ≠ (0 : α) ∧ safeDivResult a b err = toString (a / b)) := by
  unfold safeDivResult
  by_cases h : b = (0 : α)
  · left; simp [h]
  · right; simp [h]

namespace Int

/-! ### Fraction reduction -/

/-- Reduce a signed fraction `(n, d)` to an irreducible form by dividing both
numerator and denominator by `Nat.gcd (Int.natAbs n) d`.

The denominator `d` should be positive for a meaningful result. When `n = 0`,
the reduced form is `(0, 1)`. -/
def reduceFraction (n : Int) (d : Nat) : Int × Nat :=
  if n = 0 then (0, 1)
  else
    let g : Nat := Nat.gcd (Int.natAbs n) d
    let n' : Int := n / Int.ofNat g
    let d' : Nat := d / g
    (n', d')

/-! ### Reduce integer pair by gcd -/

/-- Reduce a pair of integers to coprime form by dividing both components by their gcd.
Returns `(a/g, b/g)` where `g = Int.gcd a b`.
When both arguments are zero, `gcd = 0` and division is defined as `0 / 0 = 0`. -/
def reduceByGcd (a b : ℤ) : ℤ × ℤ :=
  let g := Int.gcd a b
  (a / (g : ℤ), b / (g : ℤ))

/-- After dividing by their gcd, the resulting integers are coprime when the second argument
is nonzero. Apply with swapped arguments for the symmetric case. -/
lemma gcd_div_gcd_eq_one {a b : ℤ} (hb : b ≠ 0) :
    Int.gcd (a / (Int.gcd a b : ℤ)) (b / (Int.gcd a b : ℤ)) = 1 := by
  have h_coe_gcd : (Int.gcd a b : ℤ) = GCDMonoid.gcd a b := by
    simpa using (Int.coe_gcd a b)
  have h_coprime : IsCoprime (a / GCDMonoid.gcd a b) (b / GCDMonoid.gcd a b) :=
    isCoprime_div_gcd_div_gcd hb
  have h' : IsCoprime (a / (Int.gcd a b : ℤ)) (b / (Int.gcd a b : ℤ)) := by
    simpa [h_coe_gcd] using h_coprime
  exact (Int.isCoprime_iff_gcd_eq_one.mp h')

/-- If the denominator is nonzero, then `Int.gcd n d` is positive.
This is useful when reasoning about fraction simplification where the denominator
cannot be zero. -/
theorem gcd_pos_of_denominator_ne_zero {n d : ℤ} (h : d ≠ 0) : 0 < Int.gcd n d := by
  have h_natAbs_ne_zero : Int.natAbs d ≠ 0 := (Int.natAbs_ne_zero.mpr h)
  have hgcd_ne_zero : Int.gcd n d ≠ 0 := by
    simpa [Int.gcd] using Nat.gcd_ne_zero_right h_natAbs_ne_zero
  exact Nat.pos_of_ne_zero hgcd_ne_zero

/-- If `d ∣ a`, `0 < d`, and `0 < a`, then `0 < a / d` (in `ℤ`). This is the integer
division analogue of `Nat.div_pos`. -/
lemma ediv_pos_of_dvd_of_pos {a d : ℤ} (hdvd : d ∣ a) (hd_pos : 0 < d) (ha_pos : 0 < a) :
    0 < a / d := by
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra! hk_nonpos
    have hprod_nonpos : d * k ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hk_nonpos
    linarith
  have hdiv_eq : a / d = k :=
    Int.ediv_eq_of_eq_mul_right (by linarith) hk
  rw [hdiv_eq]
  exact hk_pos

/-- When `0 < b`, dividing `b` by `Int.gcd a b` yields a positive integer. Useful for
showing that the reduced denominator of a fraction is positive. -/
lemma ediv_gcd_pos_of_pos_right {a b : ℤ} (hb_pos : 0 < b) : 0 < b / (Int.gcd a b : ℤ) := by
  have hb_ne_zero : b ≠ 0 := by linarith
  have hg_pos : 0 < Int.gcd a b :=
    Int.gcd_pos_of_ne_zero_right a hb_ne_zero
  have hg_dvd_b : (Int.gcd a b : ℤ) ∣ b :=
    Int.gcd_dvd_right (a := a) (b := b)
  exact ediv_pos_of_dvd_of_pos hg_dvd_b (by exact_mod_cast hg_pos) hb_pos

/-! ### Fraction simplification -/

/-- Simplify a fraction to reduced form with a positive denominator.
Given `num / den` with `den ≠ 0`, both components are divided by their gcd,
then the sign is normalized so the denominator is positive.

This extends `reduceByGcd` with a sign-normalization step: if the resulting
denominator is positive, the pair is returned as-is; otherwise both components
are negated. -/
def simplifyFraction (num den : ℤ) (hden : den ≠ 0) : ℤ × ℤ :=
  let p := reduceByGcd num den
  if p.2 > 0 then p else (-p.1, -p.2)

end Int

namespace Int


/-! ### Safe integer division (Option-returning) -/

/-- Safe integer division: returns `none` when the divisor is zero,
    otherwise `some (a / b)`. -/
def safeDiv (a b : Int) : Option Int :=
  if b = 0 then none else some (a / b)


lemma safeDiv_eq_none_of_zero (a b : Int) (h : b = 0) : safeDiv a b = none := by
  simp [safeDiv, h]


lemma safeDiv_eq_some_of_ne_zero (a b : Int) (h : b ≠ 0) : safeDiv a b = some (a / b) := by
  simp [safeDiv, h]

/-- Safe integer division returning a `String`: returns `zeroMsg` when `b = 0`,
    otherwise returns `toString (a / b)`.
This is the display-oriented counterpart of `Int.safeDiv` (which returns `Option Int`). -/
def safeDivStr (zeroMsg : String) (a b : Int) : String :=
  if b = 0 then zeroMsg else toString (a / b)

/-- If the divisor is zero, `safeDivStr` returns the error message. -/

lemma safeDivStr_eq_of_zero (zeroMsg : String) (a b : Int) (h : b = 0) : safeDivStr zeroMsg a b = zeroMsg := by
  unfold safeDivStr; simp [h]

/-- If the divisor is nonzero, `safeDivStr` returns the string representation of the quotient. -/

lemma safeDivStr_eq_of_ne_zero (zeroMsg : String) (a b : Int) (h : b ≠ 0) : safeDivStr zeroMsg a b = toString (a / b) := by
  unfold safeDivStr; simp [h]

/-- `Int.safeDivStr` is the `Int` specialization of the generic `safeDivResult`. -/

lemma safeDivStr_eq_safeDivResult (zeroMsg : String) (a b : Int) : safeDivStr zeroMsg a b = safeDivResult a b zeroMsg :=
  rfl



/-! ### Integer mean of a list with a projection -/

/-- Compute the integer mean (average) of `f` applied to each element of `xs`.
Returns `0` for an empty list. Uses integer division, so the result is truncated
toward zero (or zero for an empty list).

This is equivalent to `((xs.map f).sum) / (xs.length : ℤ)`, but explicitly handles
the empty-list case for clarity. -/
def mapAvg {α : Type} (xs : List α) (f : α → Int) : Int :=
  match xs with
  | [] => 0
  | _ :: _ => ((xs.map f).sum) / (xs.length : Int)


lemma mapAvg_nil {α : Type} (f : α → Int) : mapAvg [] f = 0 := rfl

/-! ### Integer average via Euclidean (floored) division -/

/-- Integer average of a list, computed via `Int.ediv` (floored division, rounding
toward `-∞`). For the empty list, returns `0` (by `Int.ediv 0 0 = 0`). Callers
should ensure the list is non-empty for meaningful results.

Unlike `mapAvg` which uses `/` (truncating division toward `0`), this definition
uses `Int.ediv`, giving consistent downward rounding even for negative sums. -/
def listAverage (xs : List Int) : Int :=
  Int.ediv xs.sum (Int.ofNat xs.length)


lemma listAverage_nil : listAverage [] = 0 := rfl

/-- On a nonempty list, `listAverage` equals the sum divided by the length using
`Int.ediv`. -/
lemma listAverage_cons (x : Int) (xs : List Int) :
    listAverage (x :: xs) = Int.ediv ((x :: xs).sum) ((x :: xs).length : Int) := rfl

/-! ### Scaled integer average

Scaled average multiplies the sum by a `scale` factor before integer division by the length.
This is the standard technique for fixed-point arithmetic: for example, `avgScaled l 100`
computes the average in hundredths (centi-units), avoiding floating-point. -/

/-- Scaled integer average: `(l.sum * scale) / |l|`, or `0` if `l` is empty.
Generalizes fixed-point average computation for any precision factor `scale`.
For example, `avgScaled l 100` computes the average in hundredths. -/
def avgScaled (l : List Int) (scale : Int) : Int :=
  if l.isEmpty then 0 else
    l.sum * scale / (l.length : Int)


end Int
