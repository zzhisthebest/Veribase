import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-!
# `List.Pairwise` theorems

Properties of the `Pairwise` relation on lists.
-/

/--
If every element of `l` equals `v`, then `l` is pairwise equal.
-/
theorem pairwise_eq_of_forall_mem_eq (l : List α) (v : α) :
    (∀ x, x ∈ l → x = v) → List.Pairwise (fun x y => x = y) l := by
  intro h
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
      apply List.Pairwise.cons
      · intro y hy
        have hx : x = v := h x (List.mem_cons_self x xs)
        have hy' : y = v := h y (List.mem_cons_of_mem x hy)
        exact hx.trans hy'.symm
      · apply ih
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)

/--
If no element of `xs` is different from the head element, then `xs` is pairwise equal.
-/
theorem pairwise_eq_of_any_ne_head_false {α : Type} [Inhabited α] [DecidableEq α] (xs : List α)
    (h_any : xs.any (fun x => x ≠ xs[0]!) = false) :
    List.Pairwise (fun x y : α => x = y) xs := by
  apply pairwise_eq_of_forall_mem_eq xs xs[0]!
  intro x hx
  by_contra hne
  have h_true : decide (x ≠ xs[0]!) = true := decide_eq_true hne
  have h_not_true : ¬ decide (x ≠ xs[0]!) = true := (List.any_eq_false.mp h_any) x hx
  exact h_not_true h_true

/--
If `xs` is not pairwise equal, then `xs` is nonempty and there exists an element
different from the head.
-/
theorem not_pairwise_eq_imp_head_any {α : Type} [Inhabited α] [DecidableEq α] {xs : List α}
    (h_pairwise : ¬ List.Pairwise (fun x y : α => x = y) xs) :
    xs ≠ [] ∧ xs.any (fun x => x ≠ xs[0]!) := by
  constructor
  · intro h_nil
    subst xs
    exact h_pairwise (by simp)
  · by_cases h_any : xs.any (fun x => x ≠ xs[0]!) = true
    · exact h_any
    · have h_any_false : xs.any (fun x => x ≠ xs[0]!) = false :=
        Bool.eq_false_iff.mpr h_any
      exact False.elim (h_pairwise (pairwise_eq_of_any_ne_head_false xs h_any_false))

/--
Connects the Boolean decision of pairwise equality to the constructive properties:
if `decide` affirms pairwise equality then it holds, otherwise the list is nonempty
and contains an element differing from the head.
-/
theorem pairwise_eq_decide_spec {α : Type} [Inhabited α] [DecidableEq α] (xs : List α) :
    (decide (List.Pairwise (fun x y : α => x = y) xs) → List.Pairwise (fun x y : α => x = y) xs) ∧
    (¬ decide (List.Pairwise (fun x y : α => x = y) xs) → xs ≠ [] ∧ xs.any (fun x => x ≠ xs[0]!)) := by
  constructor
  · exact of_decide_eq_true
  · intro h_result
    apply not_pairwise_eq_imp_head_any
    intro h_pairwise
    exact h_result (decide_eq_true h_pairwise)

end List

end Specific
