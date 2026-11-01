import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Repeating and duplicating list elements -/

/-- Repeat each element of `xs` `n` times. -/
def repeatEach {α : Type u} (n : Nat) (xs : List α) : List α :=
  List.flatMap (fun x => List.replicate n x) xs

/-- The length of `repeatEach n xs` is `xs.length * n`. -/
theorem length_repeatEach {α : Type u} (n : Nat) (xs : List α) :
    (repeatEach n xs).length = xs.length * n := by
  induction xs with
  | nil => simp [repeatEach]
  | cons x xs ih =>
      calc
        (repeatEach n (x :: xs)).length = n + (repeatEach n xs).length := by
          simp [repeatEach]
        _ = n + xs.length * n := by rw [ih]
        _ = (x :: xs).length * n := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- Duplicate each element of `xs` (same as `repeatEach 2 xs`). -/
def duplicateEach {α : Type u} (xs : List α) : List α :=
  repeatEach 2 xs

/-- The length of `duplicateEach xs` is `xs.length * 2`. -/
theorem length_duplicateEach {α : Type u} (xs : List α) :
    (duplicateEach xs).length = xs.length * 2 := by
  simpa [duplicateEach] using length_repeatEach (α := α) 2 xs

end List

end Specific
