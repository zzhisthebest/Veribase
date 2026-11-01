import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-!
# `List.all` and `List.any` theorems

Relationships between the `all` (universal quantifier) and `any` (existential
quantifier) predicates on lists.
-/

/--
If for every `x` where `p x` is false, `q x` is true, then "not all `p`"
implies "some `q`".
-/
theorem any_of_not_all_of_false {α : Type} (p q : α → Bool) (xs : List α)
    (h_false : ∀ x, p x = false → q x = true) :
    ¬ xs.all p → xs.any q := by
  intro h
  have h_all_false : xs.all p = false := Bool.eq_false_iff.mpr h
  rcases List.all_eq_false.mp h_all_false with ⟨x, hx_mem, hx_false⟩
  exact List.any_eq_true.mpr
    ⟨x, hx_mem, h_false x (Bool.eq_false_iff.mpr hx_false)⟩

/--
If not all elements of `l` equal `v`, then there exists an element in `l` that is
not equal to `v`.
-/
theorem any_ne_of_not_all_eq [DecidableEq α] (l : List α) (v : α) :
    (l.all fun x => decide (x = v)) = false → l.any (fun x => x ≠ v) = true := by
  intro h
  rcases (List.all_eq_false).mp h with ⟨x, hxmem, hxfalse⟩
  have hxne : x ≠ v := by
    intro heq
    apply hxfalse
    exact decide_eq_true heq
  exact (List.any_eq_true).mpr ⟨x, hxmem, decide_eq_true hxne⟩

/--
If every element of `xs` is also in `ys`, then checking `xs.all (fun a => decide (a ∈ ys))`
returns `true`.
-/
theorem all_mem_of_forall_mem {α : Type u} [DecidableEq α] {xs ys : List α}
    (h : ∀ a, a ∈ xs → a ∈ ys) :
    xs.all (fun a => decide (a ∈ ys)) = true := by
  rw [List.all_eq_true]
  intro a ha
  exact decide_eq_true (h a ha)

end List

end Specific
