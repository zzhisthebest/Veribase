namespace Specific

open _root_.List

/-! ## Float rounding utilities -/

/-- Rounds `x` to the nearest multiple of `1/scale`. Computes `Float.round (x * scale) / scale`.

This is useful for fixed-precision rounding: for example, `roundScaled 100.0 x` rounds
`x` to two decimal places (nearest hundredth). -/
def Float.roundScaled (scale x : Float) : Float :=
  Float.round (x * scale) / scale

end Specific
