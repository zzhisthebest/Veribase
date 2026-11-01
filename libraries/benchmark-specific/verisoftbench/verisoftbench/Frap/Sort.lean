import Frap.Sort

/-!
# Permutation lemmas for `Frap.Sort`

Supplementary theorems about `Frap.Sort.Permutation` that extend the repo's
existing permutation library.  In particular, this module proves `permutation_middle`
(which is stated in `Frap.Sort` with `sorry` under the name `perm_swap_cons_append`)
and provides useful derived lemmas for commuting and swapping elements in list
expressions involving `++`.
-/

set_option quotPrecheck false
open Permutation

/--
**Permutation middle**: a single element can be swapped from the front of an
appended list to the middle.

This proves `permutation_middle` from `Frap.Sort` (stated there by that name with `sorry`).
We use the name `perm_swap_cons_append` to avoid a name collision with the unproven
`permutation_middle` in the repo.
-/
theorem perm_swap_cons_append {α : Type} (a : α) (l₁ l₂ : List α)
    : Permutation (a :: l₁ ++ l₂) (l₁ ++ a :: l₂) := by
  induction l₁ with
  | nil =>
    simp
    apply permutation_refl
  | cons b l₃ ih =>
    simp
    apply perm_trans
    · apply perm_swap
    · apply perm_skip
      exact ih

/--
Move an element past a middle segment: `l₁ ++ x :: l₂ ++ l₃` is a permutation of
`l₁ ++ l₂ ++ x :: l₃`.
-/
theorem perm_swap_mid_append {α : Type} (x : α) (l₁ l₂ l₃ : List α)
    : Permutation (l₁ ++ x :: l₂ ++ l₃) (l₁ ++ l₂ ++ x :: l₃) := by
  induction l₁ with
  | nil =>
    simpa using perm_swap_cons_append x l₂ l₃
  | cons a l₁' ih =>
    apply perm_skip
    exact ih

/--
Append is commutative up to permutation: `l ++ l'` is a permutation of `l' ++ l`.
-/
theorem permutation_app_comm {α : Type} (l l' : List α)
    : Permutation (l ++ l') (l' ++ l) := by
  induction l with
  | nil =>
    simp
    apply permutation_refl
  | cons a l₁ ih =>
    simp
    have h1 : Permutation (a :: (l₁ ++ l')) (a :: (l' ++ l₁)) := by
      apply perm_skip
      exact ih
    have h2 : Permutation (a :: (l' ++ l₁)) (l' ++ a :: l₁) :=
      perm_swap_cons_append a l' l₁
    apply perm_trans
    · exact h1
    · exact h2

/--
Move two cons'd elements past the first segment of an append:
`a :: b :: (l₁ ++ l₂)` permutes to `l₁ ++ a :: b :: l₂`.
-/
theorem perm_swap_cons_append2 {α : Type} (a b : α) (l₁ l₂ : List α) :
    Permutation (a :: b :: (l₁ ++ l₂)) (l₁ ++ a :: b :: l₂) :=
  perm_trans (a :: b :: (l₁ ++ l₂)) (a :: (l₁ ++ b :: l₂)) (l₁ ++ a :: b :: l₂)
    (perm_skip a (b :: (l₁ ++ l₂)) (l₁ ++ b :: l₂) (perm_swap_cons_append b l₁ l₂))
    (perm_swap_cons_append a l₁ (b :: l₂))

/--
Move two cons'd elements into respective positions between three segments:
`a :: b :: (l₁ ++ l₂ ++ l₃)` permutes to `l₁ ++ a :: l₂ ++ b :: l₃`.
-/
theorem perm_swap_cons_append3 {α : Type} (a b : α) (l₁ l₂ l₃ : List α) :
    Permutation (a :: b :: (l₁ ++ l₂ ++ l₃)) (l₁ ++ a :: l₂ ++ b :: l₃) := by
  have hstep1 : Permutation (b :: (l₁ ++ l₂ ++ l₃)) (l₁ ++ l₂ ++ b :: l₃) :=
    perm_swap_cons_append b (l₁ ++ l₂) l₃
  have hstep2 : Permutation (a :: b :: (l₁ ++ l₂ ++ l₃))
      (a :: (l₁ ++ l₂ ++ b :: l₃)) :=
    perm_skip a (b :: (l₁ ++ l₂ ++ l₃)) (l₁ ++ l₂ ++ b :: l₃) hstep1
  have hstep3 : Permutation (a :: (l₁ ++ l₂ ++ b :: l₃))
      (l₁ ++ a :: l₂ ++ b :: l₃) := by
    have htemp : Permutation (a :: (l₁ ++ (l₂ ++ b :: l₃)))
        (l₁ ++ a :: (l₂ ++ b :: l₃)) :=
      perm_swap_cons_append a l₁ (l₂ ++ b :: l₃)
    simpa using htemp
  apply perm_trans (a :: b :: (l₁ ++ l₂ ++ l₃)) (a :: (l₁ ++ l₂ ++ b :: l₃))
      (l₁ ++ a :: l₂ ++ b :: l₃) hstep2 hstep3

/--
If `l` permutes to `l₁ ++ l₂`, then `a :: l` permutes to `l₁ ++ a :: l₂`.
This lifts a cons through a permutation into the middle of the append.
-/
theorem perm_lift_cons_append {α : Type} (a : α) {l l₁ l₂ : List α}
    (h : Permutation l (l₁ ++ l₂)) : Permutation (a :: l) (l₁ ++ a :: l₂) := by
  have h_skip : Permutation (a :: l) (a :: (l₁ ++ l₂)) :=
    perm_skip a l (l₁ ++ l₂) h
  exact perm_trans (a :: l) (a :: (l₁ ++ l₂)) (l₁ ++ a :: l₂)
    h_skip (perm_swap_cons_append a l₁ l₂)
