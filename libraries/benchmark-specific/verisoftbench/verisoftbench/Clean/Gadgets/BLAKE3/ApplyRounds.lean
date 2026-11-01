import Clean.Gadgets.BLAKE3.ApplyRounds

/-!
Lemmas about the BLAKE3 `ApplyRounds` circuit from `Clean.Gadgets.BLAKE3.ApplyRounds`.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.BLAKE3.ApplyRounds

/-- Soundness of the `ApplyRounds` circuit: the elaborated circuit with
`Assumptions` and `Spec` satisfies the `Soundness (F p)` property. -/
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  exact circuit.soundness

end Gadgets.BLAKE3.ApplyRounds
