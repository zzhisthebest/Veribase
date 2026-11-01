import Clean.Tables.Fibonacci32
import Clean.Table.Basic
import Clean.Types.U32

/-!
Lemmas about the Fibonacci32 table from `Clean.Tables.Fibonacci32`.

These lemmas describe the logical consequences of the table constraints holding,
extracting the soundness guarantees in terms of the actual row values.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)] {α : Type}

namespace Tables.Fibonacci32

/--
If the `recursiveRelation` constraints hold on a two-row window `curr, next`,
then `curr.y = next.x` and, assuming both `curr.x` and `curr.y` are normalized U32 values,
`next.y.value = (curr.x.value + curr.y.value) % 2^32` and `next.y` is normalized.
-/
lemma recursiveRelation_constraints (curr next : Row (F p) RowType) (aux_env : Environment (F p))
  : recursiveRelation.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ aux_env →
  curr.y = next.x ∧
  (curr.x.Normalized → curr.y.Normalized → next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.Normalized) := by
  have eval_components {α : Type → Type} [ProvableStruct α]
      (env : Environment (F p)) (x : Var α (F p)) :
      ProvableType.eval env x = ProvableStruct.eval env x := by
    have aux : ∀ (cs : List ProvableStruct.WithProvableType)
        (as : ProvableStruct.ProvableTypeList (Expression (F p)) cs),
        ProvableStruct.eval.go env cs as =
          ProvableStruct.componentsFromElements cs
            ((ProvableStruct.componentsToElements cs as).map (Expression.eval env)) := by
      intro cs
      induction cs with
      | nil => intro as; cases as; rfl
      | cons c cs ih =>
        intro as
        cases as with
        | cons a as =>
          simp only [ProvableStruct.componentsToElements, ProvableStruct.componentsFromElements,
            ProvableStruct.eval.go, ProvableType.eval, toVars]
          rw [Vector.map_append, Vector.cast_take_append_of_eq_length,
            Vector.cast_drop_append_of_eq_length]
          congr 1
          exact ih as
    symm
    simp only [ProvableStruct.eval, ProvableType.eval, fromElements, toVars, toElements, size]
    congr 1
    apply aux
  intro h
  have hv := fib_vars curr next aux_env
  simp only [TableConstraint.ConstraintsHoldOnWindow] at h
  generalize he : recursiveRelation.windowEnv ⟨<+> +> curr +> next, rfl⟩ aux_env = env at h hv
  simp only [TableConstraint.operations, recursiveRelation,
    assignU32, table_norm, circuit_norm, Gadgets.Addition32.circuit,
    Gadgets.Addition32.elaborated] at h
  rcases hv with ⟨hx, hy, hnextx, hnexty⟩
  have hin : eval env (Gadgets.Addition32.Inputs.mk (varFromOffset U32 0)
      (varFromOffset U32 4)) = Gadgets.Addition32.Inputs.mk curr.x curr.y := by
    rw [eval_components]
    change Gadgets.Addition32.Inputs.mk (eval env (varFromOffset U32 0))
      (eval env (varFromOffset U32 4)) = _
    rw [hx, hy]
  have hout : U32.mk (env.get 16) (env.get 18) (env.get 20) (env.get 22) = next.y := by
    simpa only [↓eval_components, circuit_norm, explicit_provable_type] using hnexty
  simp only [Nat.reduceAdd, hin, Gadgets.Addition32.Assumptions,
    Gadgets.Addition32.Spec, Gadgets.Equality.circuit, hy, hnextx, hout,
    true_implies] at h
  exact ⟨h.2, fun hx hy => h.1 ⟨hx, hy⟩⟩

end Tables.Fibonacci32
