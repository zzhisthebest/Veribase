import Mathlib

namespace Char


/-! ### Character to code-point string -/

/-- Convert a character to the decimal string representation of its Unicode code point.
For example, `toNatString 'A' = "65"` and `toNatString 'a' = "97"`.
This is useful for printing ASCII values or building diagnostic strings. -/
def toNatString (c : Char) : String :=
  toString (Char.toNat c)



/-! ### Digit value conversion -/

/-- Convert a decimal digit character to its numeric value (0–9).
Returns `c.toNat - '0'.toNat`, which yields sensible results only when `c` is a
decimal digit (`'0'`–`'9'`). For other characters the result is mathematically
well-defined but semantically meaningless.

For example: `digitToNat '0' = 0`, `digitToNat '5' = 5`, `digitToNat '9' = 9`.

This is commonly used in string-to-number parsing, e.g. when folding over a
string of digits to compute its integer value. -/
def digitToNat (c : Char) : Nat :=
  c.toNat - Char.toNat '0'

/-- For a decimal digit character `c`, `digitToNat c` is strictly less than 10. -/
lemma digitToNat_lt_10 (c : Char) (hc : '0' ≤ c ∧ c ≤ '9') : digitToNat c < 10 := by
  rcases hc with ⟨hlo, hhi⟩
  have hlo_val : Char.toNat '0' ≤ Char.toNat c := (Char.le_def.mp hlo)
  have hhi_val : Char.toNat c ≤ Char.toNat '9' := (Char.le_def.mp hhi)
  unfold digitToNat
  have h0n : Char.toNat '0' = 48 := by decide
  have h9n : Char.toNat '9' = 57 := by decide
  -- hlo_val: 48 ≤ c.toNat, hhi_val: c.toNat ≤ 57
  have hlo' : 48 ≤ Char.toNat c := by simpa [h0n] using hlo_val
  have hhi' : Char.toNat c ≤ 57 := by simpa [h9n] using hhi_val
  simpa [h0n] using (by
    have h : Char.toNat c ≤ 57 := hhi'
    omega)

/-- Convert a character to its numeric digit value in the given `base`.
    Supports decimal digits `'0'`–`'9'` (values 0–9), and hexadecimal letters
    `'a'`–`'f'` / `'A'`–`'F'` (values 10–15).
    Returns `none` if the character is not a valid digit in the given base
    (i.e., the character's numeric value is ≥ `base`, or the character is
    not a digit character at all).

    For example:
    * `digitValue '5' 10 = some 5`
    * `digitValue 'A' 16 = some 10`
    * `digitValue '5' 5 = none` (digit 5 is not valid in base 5)
    * `digitValue 'G' 16 = none` (not a hexadecimal digit) -/
def digitValue (c : Char) (base : Nat) : Option Nat :=
  match c with
  | '0' => some 0
  | '1' => some 1
  | '2' => if base > 2 then some 2 else none
  | '3' => if base > 3 then some 3 else none
  | '4' => if base > 4 then some 4 else none
  | '5' => if base > 5 then some 5 else none
  | '6' => if base > 6 then some 6 else none
  | '7' => if base > 7 then some 7 else none
  | '8' => if base > 8 then some 8 else none
  | '9' => if base > 9 then some 9 else none
  | 'a' | 'A' => if base > 10 then some 10 else none
  | 'b' | 'B' => if base > 11 then some 11 else none
  | 'c' | 'C' => if base > 12 then some 12 else none
  | 'd' | 'D' => if base > 13 then some 13 else none
  | 'e' | 'E' => if base > 14 then some 14 else none
  | 'f' | 'F' => if base > 15 then some 15 else none
  | _ => none

/-- Check if a character is a hexadecimal digit (`'0'`–`'9'`, `'a'`–`'f'`, `'A'`–`'F'`). -/
def isHexChar (c : Char) : Bool :=
  c.isDigit ||
    decide ('a' ≤ c ∧ c ≤ 'f') ||
    decide ('A' ≤ c ∧ c ≤ 'F')

/-- Prop: character is a hexadecimal digit (`'0'`–`'9'`, `'a'`–`'f'`, `'A'`–`'F'`). -/
def IsHexChar (c : Char) : Prop :=
  c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

/-- Equivalence between the Bool and Prop versions of hex character check. -/
lemma isHexChar_iff (c : Char) : isHexChar c ↔ IsHexChar c := by
  unfold isHexChar IsHexChar
  simp [or_assoc]

/-- Convert a hexadecimal digit character to its numeric value (0–15).
Handles both uppercase (`'A'`–`'F'`) and lowercase (`'a'`–`'f'`) letters,
plus decimal digits (`'0'`–`'9'`). Returns `none` for non-hex characters.

For example:
* `hexDigitToNat '0' = some 0`
* `hexDigitToNat 'A' = some 10`
* `hexDigitToNat 'f' = some 15`
* `hexDigitToNat 'G' = none`

This is the inverse of `String.natToHexChar` on the domain `d < 16`. -/
def hexDigitToNat (c : Char) : Option Nat :=
  match c with
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'A' | 'a' => some 10
  | 'B' | 'b' => some 11
  | 'C' | 'c' => some 12
  | 'D' | 'd' => some 13
  | 'E' | 'e' => some 14
  | 'F' | 'f' => some 15
  | _   => none

/-- If `c.isDigit` holds, then `c` is a hex character (Bool version). -/
lemma isHexChar_of_isDigit {c : Char} (h : c.isDigit) : isHexChar c := by
  unfold isHexChar; simp [h]

/-- If `c.isDigit` holds, then `c` is a hex character (Prop version). -/
lemma IsHexChar.of_isDigit {c : Char} (h : c.isDigit) : IsHexChar c :=
  Or.inl h

/-- The decimal digit `'0'` is a hex character. -/
lemma isHexChar_0 : isHexChar '0' := by
  unfold isHexChar; simp

/-! ### Hex digit character generation -/

/-- Convert a natural number to a hex digit character (`'0'`–`'9'`, `'a'`–`'f'`)
by taking the number modulo `16` and using `Nat.digitChar`.
For example, `hexDigitChar 0 = '0'`, `hexDigitChar 10 = 'a'`, `hexDigitChar 15 = 'f'`,
`hexDigitChar 16 = '0'` (since `16 % 16 = 0`). -/
def hexDigitChar (n : Nat) : Char := Nat.digitChar (n % 16)

/-- For `d < 16`, `Nat.digitChar d` is either a decimal digit (`'0'`–`'9'`)
or a lowercase hex letter (`'a'`–`'f'`). -/
lemma digitChar_isHex (d : Nat) (hd : d < 16) :
    (Nat.digitChar d).isDigit ∨ ('a' ≤ Nat.digitChar d ∧ Nat.digitChar d ≤ 'f') := by
  have hle : d ≤ 15 := by omega
  interval_cases d <;> decide



/-! ### Binary digit conversion -/

/-- Map binary digit characters to their numeric values: `'0' → 0`, `'1' → 1`, others → 0.
This is the binary counterpart of `digitToNat` (which maps decimal digits `'0'`–`'9'` to 0–9).
For example:
* `binaryDigitToNat '0' = 0`
* `binaryDigitToNat '1' = 1`
* `binaryDigitToNat 'a' = 0` -/
def binaryDigitToNat (c : Char) : Nat :=
  match c with
  | '0' => 0
  | '1' => 1
  | _   => 0


lemma binaryDigitToNat_zero : binaryDigitToNat '0' = 0 := rfl


lemma binaryDigitToNat_one : binaryDigitToNat '1' = 1 := rfl

/-! ### Decimal digit conversion -/

/-- Map decimal digit characters to their numeric values: `'0'→0`, …, `'9'→9`, others → 0.
This is the total (non-`Option`) counterpart of `Char.hexDigitToNat` restricted to decimal digits,
and the decimal analog of `binaryDigitToNat`. Unlike `digitToNat` (which uses subtraction and is
only meaningful for digit characters), this function is safe for all characters: it returns 0
for non-digit inputs without producing arbitrary results.

For example:
* `decimalDigitToNat '0' = 0`
* `decimalDigitToNat '5' = 5`
* `decimalDigitToNat '9' = 9`
* `decimalDigitToNat 'a' = 0` -/
def decimalDigitToNat (c : Char) : Nat :=
  match c with
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _   => 0

/-- For any character `c`, `decimalDigitToNat c` is strictly less than 10.
This holds unconditionally because non-digit characters are mapped to 0.
This is a key lemma for reasoning about digit parsing with `decimalDigitToNat`. -/
lemma decimalDigitToNat_lt_10 (c : Char) : decimalDigitToNat c < 10 := by
  unfold decimalDigitToNat
  split <;> norm_num



/-! ### Base-36 digit character (uppercase) -/

/-- Convert a digit (0-35) to its uppercase character representation:
0-9 → '0'-'9', 10-35 → 'A'-'Z'.
For values ≥ 36 the result is mathematically well-defined but semantically meaningless. -/
def digitCharUpper (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (55 + d)


end Char
