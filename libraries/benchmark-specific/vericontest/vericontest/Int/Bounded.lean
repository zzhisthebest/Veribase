import Mathlib

namespace Int

/-! ### Signed integer bounds

These constants define the minimum and maximum values for signed 32-bit (`i32Min`, `i32Max`)
and signed 64-bit (`i64Min`, `i64Max`) integers. They are used throughout competitive
programming problems for overflow-checked arithmetic. -/

/-- Minimum value of a signed 32-bit integer: `-2^31`. -/
def i32Min : Int := -2147483648

/-- Maximum value of a signed 32-bit integer: `2^31 - 1`. -/
def i32Max : Int := 2147483647

/-- Minimum value of a signed 64-bit integer: `-2^63`. -/
def i64Min : Int := -9223372036854775808

/-- Maximum value of a signed 64-bit integer: `2^63 - 1`. -/
def i64Max : Int := 9223372036854775807

/-! ### Bounded arithmetic

These operations compute `a + b` or `a - b` and return the result only if it
lies within `[lo, hi]`; otherwise they return a caller-specified `fallback` value.
This generalizes the pattern of `checked_add_or` / `checked_sub_or` with hardcoded
i64 bounds to arbitrary bounds. -/

/-- Returns `a + b` if `lo ≤ a + b ≤ hi`, otherwise returns `fallback`. -/
def boundedAdd (a b lo hi fallback : Int) : Int :=
  let s := a + b
  if lo ≤ s ∧ s ≤ hi then s else fallback

/-- Returns `a - b` if `lo ≤ a - b ≤ hi`, otherwise returns `fallback`. -/
def boundedSub (a b lo hi fallback : Int) : Int :=
  let s := a - b
  if lo ≤ s ∧ s ≤ hi then s else fallback

/-- Returns `a + b` if it fits within signed 32-bit integer bounds
(`i32Min ≤ a + b ≤ i32Max`), otherwise returns `fallback`.
This is a convenience specialisation of `boundedAdd` for 32-bit overflow checking.
Common in competitive programming problems that require 32-bit integer arithmetic. -/
def checkedAddI32Or (a b fallback : Int) : Int :=
  boundedAdd a b i32Min i32Max fallback

end Int
