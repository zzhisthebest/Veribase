import Clean.Circuit.Basic
import Clean.Circuit.Theorems

/-!
Lemmas about `FormalCircuit` and `Circuit` from `Clean.Circuit.Basic`.
-/

variable {F : Type} [Field F]

namespace FormalCircuit

/-- A general lemma: for any `FormalCircuit`, the `soundness` field yields the explicit soundness
statement. This captures the standard `simpa [Soundness, circuit_norm]` pattern. -/
theorem soundness_apply {Φ : Type} [Field Φ] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output] (c : FormalCircuit Φ Input Output)
    (offset : ℕ) (env : Environment Φ)
    (input_var : Var Input Φ) (input : Input Φ)
    (h_eval : eval env input_var = input)
    (h_assump : c.Assumptions input)
    (h_hold : Circuit.ConstraintsHold.Soundness env
      ((c.main input_var).operations offset)) :
    c.Spec input (eval env (c.elaborated.output input_var offset)) := by
  have h_sound := c.soundness offset env input_var input h_eval h_assump h_hold
  simpa [Soundness, circuit_norm] using h_sound

end FormalCircuit

open ProvableType

/-- From `vals = eval env v` for a field vector, extract component equality at index `i`. -/
lemma eval_fields_component {F : Type} [Field F] {n : ℕ} (env : Environment F)
    (v : Var (fields n) F) (vals : fields n F) (h_eval : vals = eval env v) (i : ℕ)
    (hi : i < n) : Expression.eval env v[i] = vals[i] := by
  subst vals
  simp [ProvableType.eval_fields]

namespace Circuit

variable {α β γ : Type}

/-- The local length of a bind is the sum of the local lengths of the first circuit
and the second circuit applied to the output of the first, at the appropriate offsets.
This is the fundamental lemma for reasoning about the size of circuits composed with `>>=`. -/
theorem bind_localLength_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).localLength n = f.localLength n + (g (f.output n)).localLength (n + f.localLength n) := by
  show (f.operations n ++ (g _).operations _).localLength = _
  rw [Operations.append_localLength]

/-- The local length of a `do` block with two nested binds equals the sum of the
local lengths of all three circuit components. This follows from applying `bind_localLength_eq` twice. -/
theorem do_localLength_eq (c1 : Circuit F α) (c2 : Circuit F β)
    (c3 : α → β → Circuit F γ) (offset : ℕ) :
    (do
      let out1 ← c1
      let out2 ← c2
      c3 out1 out2).localLength offset =
    (c1.localLength offset) + (c2.localLength (offset + c1.localLength offset)) +
    (c3 (c1.output offset) (c2.output (offset + c1.localLength offset))).localLength
      (offset + c1.localLength offset + c2.localLength (offset + c1.localLength offset)) := by
  simp [bind_localLength_eq, add_assoc]

/-- The value of a circuit at a given offset is exactly the pair of its output and operations. -/
lemma circuit_val_eq (c : Circuit F α) (n : ℕ) : c n = (c.output n, c.operations n) := rfl

/-- Congruence of equality for pairs: `(a₁, b₁) = (a₂, b₂)` given `a₁ = a₂` and `b₁ = b₂`. -/
lemma pair_congr {a₁ a₂ : α} {b₁ b₂ : β} (ha : a₁ = a₂) (hb : b₁ = b₂) : (a₁, b₁) = (a₂, b₂) := by
  simp [ha, hb]

/-- Pointwise equality of circuits at a given `n` if output and operations agree there. -/
lemma circuit_eq_at {f g : Circuit F α} (n : ℕ) (h_out : f.output n = g.output n)
    (h_ops : f.operations n = g.operations n) : f n = g n := by
  calc
    f n = (f.output n, f.operations n) := circuit_val_eq f n
    _ = (g.output n, g.operations n) := pair_congr h_out h_ops
    _ = g n := (circuit_val_eq g n).symm

/-- Equality of circuits implies equality of outputs at each offset. -/
lemma circuit_output_congr {f g : Circuit F α} (h : f = g) (n : ℕ) : f.output n = g.output n := by
  subst h; rfl

/-- Equality of circuits implies equality of operations at each offset. -/
lemma circuit_operations_congr {f g : Circuit F α} (h : f = g) (n : ℕ) : f.operations n = g.operations n := by
  subst h; rfl

/-- Two circuits are equal iff their outputs and operations agree at every offset. -/
lemma circuit_eq_iff (f g : Circuit F α) :
    f = g ↔ (∀ n, f.output n = g.output n ∧ f.operations n = g.operations n) := by
  constructor
  · intro h n
    exact ⟨circuit_output_congr h n, circuit_operations_congr h n⟩
  · intro h
    funext n
    exact circuit_eq_at n (h n).1 (h n).2

/-- Extensionality for `Circuit`: prove equality by showing outputs and operations agree for all `n`. -/
@[ext]
theorem ext {f g : Circuit F α}
    (h_output : ∀ n, f.output n = g.output n)
    (h_operations : ∀ n, f.operations n = g.operations n) : f = g := by
  funext n
  exact circuit_eq_at n (h_output n) (h_operations n)

/-- The output of any `Circuit F Unit` at any offset is `()` because `Unit` is a subsingleton. -/
lemma output_unit_eq {c : Circuit F Unit} {n : ℕ} : c.output n = () :=
  Subsingleton.elim _ _

end Circuit
