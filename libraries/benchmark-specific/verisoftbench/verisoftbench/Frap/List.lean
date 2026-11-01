import Frap.Exercises.IndProp

set_option quotPrecheck false

/-!
# Theorems about Frap's `Hidden.List`

This module provides theorems about `Hidden.List.append`, `Hidden.List.reverse`,
and `Hidden.List.Palindrome` from Frap's `IndProp` exercises.  These lemmas are
needed because `Frap.Exercises.IndProp` does not include them, unlike the
corresponding `Frap.Exercises.Inductive` file which only provides `append_assoc`
and `length` lemmas.
-/

namespace Hidden
namespace List

/--
Associativity of list append: `(as ++ bs) ++ cs = as ++ (bs ++ cs)`.
-/
theorem append_assoc {α : Type} (as bs cs : List α)
    : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    calc
      ((List.cons a as') ++ bs) ++ cs = (List.cons a (as' ++ bs)) ++ cs := by rw [cons_append]
      _ = List.cons a ((as' ++ bs) ++ cs) := by rw [cons_append]
      _ = List.cons a (as' ++ (bs ++ cs)) := by rw [ih]
      _ = (List.cons a as') ++ (bs ++ cs) := by rw [cons_append]

/--
Reverse distributes over append, swapping the order:
`reverse (as ++ bs) = reverse bs ++ reverse as`.
-/
theorem reverse_append {α : Type} (as bs : List α)
    : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as with
  | nil => simp [reverse, nil_append, append_nil]
  | cons a as' ih =>
    rw [cons_append]
    calc
      reverse (List.cons a (as' ++ bs)) = reverse (as' ++ bs) ++ List.cons a List.nil := rfl
      _ = (reverse bs ++ reverse as') ++ List.cons a List.nil := by rw [ih]
      _ = reverse bs ++ (reverse as' ++ List.cons a List.nil) := by rw [append_assoc]
      _ = reverse bs ++ reverse (List.cons a as') := rfl

/--
Reverse of `xs ++ [x]` distributes as `x :: reverse xs`.
-/
theorem reverse_snoc {α : Type} (xs : List α) (x : α)
    : reverse (xs ++ List.cons x List.nil) = List.cons x (reverse xs) := by
  calc
    reverse (xs ++ List.cons x List.nil) = reverse (List.cons x List.nil) ++ reverse xs := by
      rw [reverse_append]
    _ = List.cons x List.nil ++ reverse xs := by rw [singleton_reverse]
    _ = List.cons x (reverse xs) := rfl

/--
Reverse of a cons-snoc pattern swaps the endpoints:
`reverse (x :: xs ++ [y]) = y :: reverse xs ++ [x]`.
-/
theorem reverse_cons_snoc {α : Type} (x : α) (xs : List α) (y : α)
    : reverse (List.cons x xs ++ List.cons y List.nil)
      = List.cons y (reverse xs ++ List.cons x List.nil) := by
  calc
    reverse (List.cons x xs ++ List.cons y List.nil)
        = reverse (xs ++ List.cons y List.nil) ++ List.cons x List.nil := rfl
    _ = (List.cons y (reverse xs)) ++ List.cons x List.nil := by rw [reverse_snoc]
    _ = List.cons y (reverse xs ++ List.cons x List.nil) := rfl

/--
Reverse is involutive: `reverse (reverse as) = as`.
-/
theorem reverse_reverse {α : Type} (as : List α) : reverse (reverse as) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    calc
      reverse (reverse (List.cons a as')) = reverse (reverse as' ++ List.cons a List.nil) := rfl
      _ = List.cons a (reverse (reverse as')) := by rw [reverse_snoc]
      _ = List.cons a as' := by rw [ih]

namespace Palindrome

/--
If `xs` is a palindrome (`reverse xs = xs`), then wrapping it with the same
element `x` on both ends preserves the palindrome property.
-/
theorem reverse_cons_snoc_eq {α : Type} (x : α) (xs : List α) (h : reverse xs = xs)
    : reverse (List.cons x xs ++ List.cons x List.nil)
      = List.cons x xs ++ List.cons x List.nil := by
  rw [reverse_cons_snoc, h, ← cons_append]

/--
If a list satisfies the `Palindrome` predicate, then `l = reverse l`.
-/
theorem Palindrome_rev_1 {α : Type} (l : List α)
    : Palindrome l → l = reverse l := by
  intro h
  induction h with
  | nil => rfl
  | single x => rfl
  | sandwich x xs _h ih =>
    exact (reverse_cons_snoc_eq x xs ih.symm).symm

/--
A list appended to its reverse is always a palindrome.
`Palindrome (l ++ reverse l)`.
-/
theorem palindrome_append_reverse {α : Type} (l : List α) : Palindrome (l ++ reverse l) := by
  induction l with
  | nil => exact Palindrome.nil
  | cons a as ih =>
    have h : (List.cons a as) ++ reverse (List.cons a as) =
             List.cons a (as ++ reverse as) ++ List.cons a List.nil := by
      calc
        (List.cons a as) ++ reverse (List.cons a as)
            = (List.cons a as) ++ (reverse as ++ List.cons a List.nil) := rfl
        _ = List.cons a (as ++ (reverse as ++ List.cons a List.nil)) := by rw [cons_append]
        _ = List.cons a ((as ++ reverse as) ++ List.cons a List.nil) := by rw [← append_assoc]
        _ = List.cons a (as ++ reverse as) ++ List.cons a List.nil := by rw [cons_append]
    rw [h]
    exact Palindrome.sandwich a (as ++ reverse as) ih

end Palindrome
end List
end Hidden
