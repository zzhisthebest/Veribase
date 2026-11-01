import Mathlib.Data.Bool.Basic

namespace Specific

open _root_.List

namespace Bool

/-! ## Case analysis lemma -/

/-- Every `Bool` is either `true` or `false`. This is the `true`-first version
of `Bool.eq_false_or_eq_true`. -/
theorem eq_true_or_eq_false (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-! ## Conditional selection -/

/-- Select between two values based on a `Bool` flag.
Equivalent to `if flag then whenTrue else whenFalse`, but as a first-class function
suitable for higher-order programming and function composition. -/
def select {α : Type u} (flag : Bool) (whenTrue whenFalse : α) : α :=
  if flag then whenTrue else whenFalse

/-- If both branches satisfy a `Prop` predicate `p`, then the result
of `select` also satisfies `p`. The flag is case-split, so this works
for any non-computable predicate. -/
theorem select_property {α : Type u} (p : α → Prop) (flag : Bool) {whenTrue whenFalse : α}
    (hTrue : p whenTrue) (hFalse : p whenFalse) :
    p (select flag whenTrue whenFalse) := by
  cases flag <;> simp [select, hTrue, hFalse]

end Bool

end Specific
