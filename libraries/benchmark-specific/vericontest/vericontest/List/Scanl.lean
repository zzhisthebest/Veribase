import Mathlib
import vericontest.List

open List

/-!
# Scanl — cumulative fold lemmas

Lemmas about `List.scanl`, which produces a list of intermediate results
of a left fold (cumulative fold). These lemmas are useful when `scanl` is used
for cumulative sums, prefix computations, and similar operations.
-/

namespace List

/-! ### Length lemma -/

/-- Length of `drop 1` on a `scanl` result equals the original list's length.
This holds for any scan function `f`, any initial value `b`, and any list `l`.
Since `scanl f b l` has length `l.length + 1`, dropping the first element
(the initial value `b`) leaves exactly `l.length` elements. -/
lemma length_drop_one_scanl (l : List α) (f : β → α → β) (b : β) :
    ((List.scanl f b l).drop 1).length = l.length := by
  rw [List.length_drop, List.length_scanl]
  omega

/-! ### Scanl with addition equals prefix sum -/

/-- The i-th element of `scanl (· + ·) b l` is `b + (l.take i).sum`.
That is, `scanl` with addition produces the cumulative sums starting from the base `b`,
and the element at index `i` equals `b` plus the sum of the first `i` elements of `l`.

Requires `i` to be in bounds of the `scanl` result (which has length `l.length + 1`). -/
lemma scanl_add_take_sum (l : List α) [AddMonoid α] (b : α) (i : ℕ)
    (h : i < (List.scanl (· + ·) b l).length) :
    (List.scanl (· + ·) b l)[i] = b + (l.take i).sum := by
  induction l generalizing b i with
  | nil =>
    have hi0 : i = 0 := by
      simp [List.scanl] at h
      omega
    subst hi0
    simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp [List.scanl]
      have hbound : i < (List.scanl (· + ·) (b + a) as).length := by
        have hlen_scanl := List.length_scanl (f := (· + · : α → α → α)) b (a :: as)
        rw [hlen_scanl, List.length_cons] at h
        have hlen_scanl2 := List.length_scanl (f := (· + · : α → α → α)) (b + a) as
        omega
      have hih := ih (b + a) i hbound
      rw [hih]
      simp [List.take, add_assoc]

end List
