import Clean.Gadgets.Rotation64.Theorems
import Mathlib.Tactic.IntervalCases

/-!
Lemmas about the Rotation64 gadget from `Clean.Gadgets.Rotation64.Theorems`.
-/

namespace Gadgets.Rotation64.Theorems

/--
Soundness of `rotRight64_u64`: for any offset `o < 8`, the byte-level rotation
`rotRight64_u64` computes the same result as the value-level `rotRight64`.
-/
theorem rotation64_bits_soundness_1 {o : ℕ} (ho : o < 8) {x : U64 ℕ} :
    (rotRight64_u64 x o).valueNat = rotRight64 x.valueNat o := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  interval_cases o <;>
    simp [rotRight64_u64, U64.valueNat, rotRight64] <;> omega

end Gadgets.Rotation64.Theorems
