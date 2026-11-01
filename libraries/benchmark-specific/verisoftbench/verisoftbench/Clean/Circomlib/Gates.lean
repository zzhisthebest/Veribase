import Clean.Circomlib.Gates
import Clean.Gadgets.Boolean
import verisoftbench.Common.Nat.Basic

/-!
Lemmas about the Circomlib gates, including `MultiAND` and helper lemmas
for foldl of bitwise AND over field element vectors.

Most of these were originally in `Clean.Circomlib.Gates` (inside the
`Circomlib.MultiAND` namespace) but are extracted here for reuse across
related proofs.
-/

variable {p : ℕ} [Fact p.Prime]

namespace Circomlib
namespace MultiAND

open IsBool

/-- For a size-2 vector of field elements with a boolean first entry,
    the foldl of bitwise AND starting from 1 equals the bitwise AND of the two entries. -/
lemma foldl_land_two (v : Vector (F p) 2) (h0 : IsBool v[0]) :
    (v.map (·.val)).foldl (· &&& ·) 1 = v[0].val &&& v[1].val := by
  have hv : v = #v[v[0], v[1]] := by
    ext i hi
    interval_cases i <;> simp
  rw [hv]
  rcases h0 with h0 | h0 <;> simp [h0, ZMod.val_one]

/-- For `n = 2`, the main circuit operations equal the operations of `assignEq` on the product. -/
lemma main_two_operations_eq (input_var : Var (fields 2) (F p)) (offset : ℕ) :
    (main input_var).operations offset =
    (HasAssignEq.assignEq (input_var[0] * input_var[1])).operations offset := by
  simp [circuit_norm, main, AND.circuit, AND.main]

/-- For `n = 2`, the main circuit output equals the output of `assignEq` on the product. -/
lemma main_two_output_eq (input_var : Var (fields 2) (F p)) (offset : ℕ) :
    (main input_var).output offset =
    (HasAssignEq.assignEq (input_var[0] * input_var[1])).output offset := by
  simp [circuit_norm, main, AND.circuit, AND.main]

/-- The `MultiAND` main circuit operations are subcircuit-consistent for all input sizes `n`. -/
theorem main_subcircuitsConsistent (n : ℕ) (input : Var (fields n) (F p)) (offset : ℕ) :
    Operations.SubcircuitsConsistent offset ((main input).operations offset) := by
  revert input offset
  refine Nat.strong_induction_on n ?_
  intro n ih input offset
  match n with
  | 0 => simp [circuit_norm, main]
  | 1 => simp [circuit_norm, main]
  | 2 =>
    unfold main
    simpa [circuit_norm, Operations.SubcircuitsConsistent] using
      AND.circuit.subcircuitsConsistent (input[0], input[1]) offset
  | n + 3 =>
    unfold main
    dsimp only
    let n1 := (n + 3) / 2
    let n2 := (n + 3) - n1
    let input1 : Var (fields n1) (F p) := input.take n1 |>.cast (by
      simp only [Nat.min_def, n1]; split <;> omega)
    let input2 : Var (fields n2) (F p) := input.drop n1 |>.cast (by omega)
    have hn1 : n1 < n + 3 := Nat.div_two_lt (n + 3) (Nat.succ_pos _)
    have hn2 : n2 < n + 3 :=
      Nat.sub_div_two_lt (n + 3) (Nat.succ_pos _)
        (Nat.div_two_pos (n + 3) (by omega))
    have ih1 : Operations.SubcircuitsConsistent offset
        ((main input1).operations offset) :=
      ih n1 hn1 input1 offset
    have ih2_at : ∀ (off : ℕ),
        Operations.SubcircuitsConsistent off ((main input2).operations off) :=
      λ off => ih n2 hn2 input2 off
    apply Circuit.subcircuitsConsistent_bind (main input1)
      (λ out1 => main input2 >>= λ out2 => AND.circuit.main (out1, out2)) offset
    · exact ih1
    · dsimp
      apply Circuit.subcircuitsConsistent_bind (main input2)
        (λ out2 => AND.circuit.main ((main input1).output offset, out2))
        (offset + (main input1).localLength offset)
      · exact ih2_at (offset + (main input1).localLength offset)
      · simpa [circuit_norm, Operations.SubcircuitsConsistent] using
          AND.circuit.subcircuitsConsistent
            ((main input1).output offset,
             (main input2).output
               (offset + (main input1).localLength offset))
            (offset + (main input1).localLength offset +
             (main input2).localLength
               (offset + (main input1).localLength offset))

end MultiAND
end Circomlib
