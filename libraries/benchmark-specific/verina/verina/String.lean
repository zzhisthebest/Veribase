import Mathlib.Data.String.Basic

namespace Specific

namespace String

/-! ## Character repetition and uniform strings -/

/-- Creates a string by repeating the character `c` `n` times. -/
def repeatChar (n : Nat) (c : Char) : String :=
  String.mk (List.replicate n c)

@[simp]
theorem repeatChar_length (n : Nat) (c : Char) : (repeatChar n c).length = n := by
  unfold repeatChar
  simp [String.length]

@[simp]
theorem repeatChar_front_succ (n : Nat) (c : Char) :
    (repeatChar (n + 1) c).front = c := by
  unfold repeatChar String.front String.get
  rw [List.replicate_succ]
  simp [String.utf8GetAux.eq_2]

/-- Constructs a uniform string from a value by extracting its length and character. -/
def uniformByLength {α : Type} (lengthOf : α → Nat) (choose : α → Char) (x : α) : String :=
  repeatChar (lengthOf x) (choose x)

@[simp]
theorem uniformByLength_length {α : Type} (lengthOf : α → Nat) (choose : α → Char) (x : α) :
    (uniformByLength lengthOf choose x).length = lengthOf x := by
  simp [uniformByLength]

end String

end Specific
