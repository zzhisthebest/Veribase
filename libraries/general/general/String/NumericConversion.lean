import Mathlib
import general.Char.BalancedDelimiters
import general.Int.Core
import general.Common.Logic
import general.List.Parsing
import general.List.Sequences
import general.List.Sort
import general.Nat.Distances

namespace String

/-! ## Decimal digit conversion -/

/-- Map a character to a zero-based index relative to a base character.
`charIdx base c` returns `c.toNat - base.toNat`. For example,
`charIdx 'a' 'c' = 2` and `charIdx '0' '5' = 5`.
This is useful for mapping alphabet characters to indices (e.g., `'a'`..`'z'` → `0`..`25`). -/
def charIdx (base c : Char) : Nat := c.toNat - base.toNat

/-- Get the numeric value of a decimal digit character.
    Returns `c.toNat - '0'.toNat`; correct for valid digits, arbitrary otherwise. -/
def decDigitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Get the numeric value of a decimal digit character as an `Int`.
    Returns `Int.ofNat (c.toNat - '0'.toNat)`; correct for valid digits, arbitrary otherwise. -/
def decDigitValInt (c : Char) : Int := Int.ofNat (c.toNat - '0'.toNat)

/-- Convert a hex digit character to its numeric value (0–15).
    Handles uppercase `'A'`–`'F'` (values 10–15) and decimal digits `'0'`–`'9'` (values 0–9).
    Assumes the character is a valid uppercase hex digit; results are well-defined but
    semantically meaningless for other characters.

    This is the total (Nat-valued) counterpart of `Char.hexDigitToNat`, which returns `Option Nat`.
    For decimal digits only, `decDigitVal` returns the same result.

    For example:
    * `charToDigit '0' = 0`
    * `charToDigit '5' = 5`
    * `charToDigit 'A' = 10`
    * `charToDigit 'F' = 15` -/
def charToDigit (c : Char) : Nat :=
  if h : c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10

/-- Convert a digit 0-9 to its character representation.
    `digitChar 0 = '0'`, `digitChar 5 = '5'`, `digitChar 9 = '9'`.
    This is the inverse of `decDigitVal` for digits 0-9. -/
def digitChar (n : Nat) : Char :=
  Char.ofNat (('0').toNat + n)


lemma digitChar_zero : digitChar 0 = '0' := by
  unfold digitChar; simp

/-- Convert a list of decimal digit characters to the corresponding `Nat`,
    processing digits most‑significant‑first.  For example `['1','2','3'] → 123`. -/
def decDigitsToNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + decDigitVal c) 0

/-- Convert a list of decimal digit characters to the corresponding `Int`,
    processing digits most‑significant‑first.  For example `['1','2','3'] → 123`.
    This is the `Int` counterpart of `decDigitsToNat`. -/
def decDigitsToInt (cs : List Char) : Int :=
  cs.foldl (fun acc c => acc * 10 + decDigitValInt c) 0

/-- Parse a list of characters as digits in the given `base` using Horner's method.
    Characters that are not valid digits in the base (per `Char.digitValue`) are
    silently ignored (they contribute nothing to the accumulated value).

    For example:
    * `digitsInBaseToNat ['1', '2', '3'] 10 = 123`
    * `digitsInBaseToNat ['1', 'A'] 16 = 26`
    * `digitsInBaseToNat ['1', '0', '1'] 2 = 5` -/
def digitsInBaseToNat (cs : List Char) (base : Nat) : Nat :=
  cs.foldl (fun acc c =>
    match Char.digitValue c base with
    | some d => acc * base + d
    | none   => acc) 0

/-- Parse a positive natural number from the front of a character list.
    Consumes the first digit (must be `'1'`–`'9'`), then reads all following digits.
    Leading zeros (including a sole `'0'`) are rejected, returning `none`.
    Returns `some (n, rest)` where `n > 0` and `rest` is the suffix after the
    consumed digits.
    For example:
    * `parsePositiveNatPrefix ['1','2','3','a','b'] = some (123, ['a','b'])`
    * `parsePositiveNatPrefix ['0','1','2'] = none`
    * `parsePositiveNatPrefix ['a','b','c'] = none` -/
def parsePositiveNatPrefix (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | [] => none
  | '0' :: _ => none
  | c :: rest =>
    if c.isDigit then
      let (digits, suffix) := List.span (·.isDigit) rest
      some (decDigitsToNat (c :: digits), suffix)
    else none

/-- Convert a decimal string to a natural number via left fold with Horner's method.
    Each character is treated as a decimal digit (via `decDigitVal`).
    Non‑digit characters produce arbitrary results.

    For example, `decimalToNat "123" = 123`. -/
def decimalToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + decDigitVal c) 0


lemma decimalToNat_nil : decimalToNat "" = 0 := by
  unfold decimalToNat String.foldl
  rw [String.foldlAux]
  exact dif_neg (by decide)

/-- Filter digit characters from a list of `Char`s and convert them to their numeric
values via `decDigitVal`. Non-digit characters are silently dropped.

For example, `filterDigits ['a','1','b','2','c'] = [1,2]`. -/
def filterDigits (chars : List Char) : List Nat :=
  chars.filterMap (fun c => if c.isDigit then some (decDigitVal c) else none)

/-- Extract all digit characters from a string, returning them as a `List Char`.
Uses `Char.isDigit` which recognizes all Unicode digit characters. -/
def digits (s : String) : List Char :=
  s.data.filter Char.isDigit


lemma digits_nil : digits "" = [] := by
  simp [digits]

lemma digits_eq_self_iff_all_digits (s : String) : digits s = s.data ↔ ∀ c ∈ s.data, Char.isDigit c := by
  simp [digits, List.filter_eq_self]

/-! ## Binary string conversion -/

/-- Convert a binary string (e.g., `"101"`) to a natural number.
Uses left fold with Horner's method: each step multiplies the accumulator by 2 and adds 1
if the current character is `'1'`, otherwise adds 0.
Characters other than `'1'` are treated as `0`. -/
def binaryToNat (s : String) : Nat :=
  s.data.foldl (fun acc c => acc * 2 + (if c = '1' then 1 else 0)) 0

/-- Interpret a string as a number in a given base with a character offset.
    Each character `c` contributes `charIdx offset c` as its digit value.
    Uses Horner's method: `foldl (fun acc c => acc * base + charIdx offset c) 0`.

    Defaults give the LeetCode 1880 convention (base 10, offset `'a'` for `'a'→0, 'b'→1, …`).
    This generalizes `decDigitsToNat` (base 10, offset `'0'`) and `binaryToNat` (base 2)
    to arbitrary bases and offsets. -/
def numVal (w : String) (base : Nat := 10) (offset : Char := 'a') : Nat :=
  w.data.foldl (fun acc c => acc * base + charIdx offset c) 0

/-- Interpret a string as a natural number in a given base using `charToDigit`
    for hex-digit-aware parsing (handles `'0'`–`'9'` and `'A'`–`'F'`).
    Uses Horner's method: `foldl (fun acc c => acc * base + charToDigit c) 0`.

    Unlike `numVal` (which uses a configurable character offset), this function uses
    `charToDigit` to directly map hex digit characters to their numeric values.
    This is the natural interpretation when the characters are hex digits.

    For example:
    * `stringValue "FF" 16 = 255`
    * `stringValue "123" 10 = 123`
    * `stringValue "1010" 2 = 10` -/
def stringValue (s : String) (base : Nat) : Nat :=
  s.toList.foldl (fun acc c => acc * base + charToDigit c) 0

/-! ## Hexadecimal conversion -/

/-- Convert a natural number `d < 16` to its uppercase hexadecimal character
    (`'0'`..`'9'`, `'A'`..`'F'`).  Returns `'0'` for out‑of‑range inputs. -/
def natToHexChar (d : Nat) : Char :=
  match d with
  | 0  => '0'  | 1  => '1'  | 2  => '2'  | 3  => '3'
  | 4  => '4'  | 5  => '5'  | 6  => '6'  | 7  => '7'
  | 8  => '8'  | 9  => '9'
  | 10 => 'A'  | 11 => 'B'  | 12 => 'C'  | 13 => 'D'
  | 14 => 'E'  | 15 => 'F'  | _  => '0'

/-- Lowercase variant of `natToHexChar`: convert a natural number `d < 16` to its
    lowercase hexadecimal character (`'0'`..`'9'`, `'a'`..`'f'`).
    Returns `'0'` for out-of-range inputs. -/
def natToHexCharLower (d : Nat) : Char :=
  match d with
  | 0  => '0'  | 1  => '1'  | 2  => '2'  | 3  => '3'
  | 4  => '4'  | 5  => '5'  | 6  => '6'  | 7  => '7'
  | 8  => '8'  | 9  => '9'
  | 10 => 'a'  | 11 => 'b'  | 12 => 'c'  | 13 => 'd'
  | 14 => 'e'  | 15 => 'f'  | _  => '0'

/-- Convert a natural number `d < 16` to its uppercase hexadecimal digit as a
    single-character `String`. This is a `String`-valued counterpart of `natToHexChar`,
    convenient for direct concatenation with `++`.
    Returns `"0"` for out‑of‑range inputs. -/
def hexDigit (d : Nat) : String :=
  String.singleton (natToHexChar d)

/-- Format a natural number as a two‑character uppercase hexadecimal string
    by extracting the high and low nibbles (division and modulo by 16).
    For values `n < 256` this produces the standard two‑digit hex byte representation;
    for larger `n`, only the least significant byte is captured.
    For example: `hexByte 255 = "FF"`, `hexByte 10 = "0A"`, `hexByte 0 = "00"`. -/
def hexByte (n : Nat) : String :=
  let hi := n / 16
  let lo := n % 16
  hexDigit hi ++ hexDigit lo

/-- Get the uppercase hexadecimal digits of `n`, most significant first.
    For `0` the result is `['0']`. -/
def natToHexDigits (n : Nat) : List Char :=
  if n = 0 then ['0']
  else
    let rec go (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else go (m / 16) (natToHexChar (m % 16) :: acc)
    go n []

/-- Convert a `Nat` to its uppercase hexadecimal string representation.
    No leading zeros except for `0` itself (`natToHexString 0 = "0"`). -/
def natToHexString (n : Nat) : String :=
  String.mk (natToHexDigits n)

/-! ## Decimal digit formatting -/

/-- Format a natural number as a zero-padded decimal string of the given `width`.
    Digits beyond `width` are truncated from the most-significant side.
    For example, `padDigits 5 2 = "05"` and `padDigits 123 4 = "0123"`. -/
def padDigits (n : Nat) (width : Nat) : String :=
  let rec go (m : Nat) (w : Nat) : List Char :=
    match w with
    | 0 => []
    | w' + 1 => digitChar (m % 10) :: go (m / 10) w'
  String.mk ((go n width).reverse)

/-- Format a natural number as a zero-padded two-digit string.
    Convenience specialization: `padTwoDigits n = padDigits n 2`.
    For example, `padTwoDigits 5 = "05"` and `padTwoDigits 42 = "42"`. -/
def padTwoDigits (n : Nat) : String :=
  padDigits n 2

/-! ## Recursive decimal string from Nat -/

/-- Convert a natural number to its decimal string representation using
a recursive algorithm. Returns `"0"` for `n = 0`. For `n > 0`, recurses on
`n / 10` and appends the digit character for `n % 10`.

This is the inverse of `decimalToNat`: `decimalToNat (decimalString n) = n`. -/
def decimalString (n : Nat) : String :=
  if h : n = 0 then "0" else
    if hq : n / 10 = 0 then
      String.singleton (digitChar (n % 10))
    else
      decimalString (n / 10) ++ String.singleton (digitChar (n % 10))
termination_by n
decreasing_by
  have hpos : 0 < n := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by norm_num : 1 < 10)


lemma decimalString_zero : decimalString 0 = "0" := by
  unfold decimalString; simp

/-! ## Generic base-N string conversion -/

/-- Convert a natural number to its string representation in base `b`.
Requires `1 < b` for termination. Returns `"0"` for `n = 0`.
For bases > 10, `digitChar` only handles digits 0–9, so this works correctly
only for bases ≤ 10.

This generalizes `decimalString` (which is the special case `b = 10`). -/
def toBaseString (b : Nat) (hb : 1 < b) (m : Nat) : String :=
  if h : m = 0 then "0" else
    if _hlt : m < b then
      String.mk [digitChar m]
    else
      toBaseString b hb (m / b) ++ String.mk [digitChar (m % b)]
termination_by m
decreasing_by
  have hpos : 0 < m := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos hb

/-- Appending a singleton character to a string multiplies the
`decimalToNat` value by 10 and adds the digit value of the character. -/
lemma decimalToNat_append_singleton (s : String) (c : Char) :
    decimalToNat (s ++ String.singleton c) = decimalToNat s * 10 + decDigitVal c := by
  simp [decimalToNat, String.foldl_eq, String.data_append, List.foldl_append]

/-- For a digit `d < 10`, the character produced by `digitChar d` is indeed a digit. -/
lemma isDigit_digitChar (d : Nat) (hd : d < 10) : (digitChar d).isDigit := by
  unfold digitChar
  interval_cases d <;> decide

/-- For a digit `d < 10`, `decDigitVal` recovers `d` from the digit character.
In other words, `decDigitVal` and `digitChar` are inverses on `{0,…,9}`. -/
lemma decDigitVal_digitChar (d : Nat) (hd : d < 10) : decDigitVal (digitChar d) = d := by
  unfold decDigitVal digitChar
  interval_cases d <;> decide

/-- Check that a string parses to a `Nat` via `String.toNat?` and the result is ≤ `n`.
Returns `false` if the string does not parse as a natural number. -/
def toNatLe (s : String) (n : Nat) : Bool :=
  match s.toNat? with
  | some m => decide (m ≤ n)
  | none => false

/-- Parse a natural-number string (no sign) as an `Int`, defaulting to `0` if parsing fails.
This is a convenience wrapper around `String.toNat?` that returns `Int` instead of `Option ℕ`.
Useful for parsing unsigned integer coefficients in algebraic expressions.

For example:
* `toNatAsInt "123" = 123`
* `toNatAsInt "" = 0`
* `toNatAsInt "abc" = 0` -/
def toNatAsInt (s : String) : Int :=
  match s.toNat? with
  | some n => Int.ofNat n
  | none   => 0

/-- Parse a string to a natural number, defaulting to 0 if parsing fails.
This is a convenience wrapper around `String.toNat?` that returns a `Nat` directly
instead of `Option Nat`. Non-numeric strings and empty strings both default to `0`.

For example:
* `parseNat "123" = 123`
* `parseNat "" = 0`
* `parseNat "abc" = 0` -/
def parseNat (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none   => 0


lemma parseNat_of_isNat (s : String) (n : Nat) (h : s.toNat? = some n) : parseNat s = n := by
  unfold parseNat
  simp [h]


lemma parseNat_nil : parseNat "" = 0 := by
  unfold parseNat; rfl

/-! ## Binary bit character conversion -/

/-- Map a bit (0 or 1) to its character representation: 0 ↦ `'0'`, nonzero ↦ `'1'`.
This is the binary counterpart of `digitChar` (which maps decimal digits 0–9). -/
def bitChar (b : Nat) : Char :=
  if b = 0 then '0' else '1'


lemma bitChar_zero : bitChar 0 = '0' := rfl


lemma bitChar_one : bitChar 1 = '1' := by
  simp [bitChar]

/-- `Char.binaryDigitToNat` inverts `bitChar` on modulo-2 residues:
`Char.binaryDigitToNat (bitChar (n % 2)) = n % 2`. -/
lemma binaryDigitToNat_bitChar_mod_two (n : Nat) :
    Char.binaryDigitToNat (bitChar (n % 2)) = n % 2 := by
  unfold bitChar Char.binaryDigitToNat
  by_cases h : n % 2 = 0
  · simp [h]
  · have h1 : n % 2 = 1 := Nat.mod_two_eq_one_of_ne_zero h
    simp [h, h1]

/-! ## Recursive binary string from Nat -/

/-- Recursively convert a natural number to its binary string representation.
Builds from MSB to LSB by recursion on `n/2`. Returns `"0"` for `n = 0`.

This is the binary analog of `decimalString`. -/
def binaryString (n : Nat) : String :=
  if n = 0 then "0"
  else
    if n / 2 = 0 then String.singleton (bitChar (n % 2))
    else binaryString (n / 2) ++ String.singleton (bitChar (n % 2))
termination_by n


lemma binaryString_zero : binaryString 0 = "0" := by
  unfold binaryString; simp

/-! ## Hexadecimal string conversion -/

/-- Convert a hexadecimal string to a natural number using Horner's method.
Each character is interpreted via `Char.hexDigitToNat`; invalid hex characters
are treated as 0 (equivalent to `(Char.hexDigitToNat c).getD 0`).

For example, `hexStringToNat "1A" = 26`, `hexStringToNat "FF" = 255`, `hexStringToNat "0" = 0`. -/
def hexStringToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (Char.hexDigitToNat c).getD 0) 0


lemma hexStringToNat_nil : hexStringToNat "" = 0 := by
  unfold hexStringToNat String.foldl
  rw [String.foldlAux]
  exact dif_neg (by decide)

/-! ## `binaryToNat` folding lemmas -/

/-- Appending a singleton character to a binary string multiplies the `binaryToNat` value
by 2 and adds the binary digit value of the character. -/
lemma binaryDigitToNat_eq_ite (c : Char) : Char.binaryDigitToNat c = if c = '1' then 1 else 0 := by
  unfold Char.binaryDigitToNat
  by_cases h1 : c = '1'
  · simp [h1]
  · by_cases h0 : c = '0'
    · simp [h0, h1]
    · simp [h0, h1]

/-- Appending a singleton character to a binary string multiplies the `binaryToNat` value
by 2 and adds the binary digit value of the character. -/
lemma binaryToNat_append_singleton (s : String) (c : Char) :
    binaryToNat (s ++ String.singleton c) =
    binaryToNat s * 2 + Char.binaryDigitToNat c := by
  simp [binaryToNat, String.data_append, List.foldl_append, binaryDigitToNat_eq_ite]

/-! ## Properties of `binaryString` -/

/-- `binaryString n` always has positive length. -/
lemma binaryString_length_pos (n : Nat) : (binaryString n).data.length > 0 := by
  induction' n using Nat.strong_induction_on with n ih
  unfold binaryString
  by_cases hzero : n = 0
  · subst hzero; decide
  · rw [if_neg hzero]
    by_cases hdiv : n / 2 = 0
    · rw [if_pos hdiv]; simp
    · rw [if_neg hdiv]; simp [String.data_append]

/-- The character data of `binaryString n` is nonempty. -/
lemma binaryString_data_ne_nil (n : Nat) : (binaryString n).data ≠ [] := by
  have hlen := binaryString_length_pos n
  intro h; rw [h] at hlen; simp at hlen

/-- For `n ≠ 0`, the binary string of `n` does not have a leading zero. -/
lemma binaryString_data_head_ne_zero (n : Nat) (hn : n ≠ 0) :
    (binaryString n).data.head! ≠ '0' := by
  induction' n using Nat.strong_induction_on with n ih
  unfold binaryString
  rw [if_neg hn]
  by_cases hdiv : n / 2 = 0
  · rw [if_pos hdiv]
    have hn1 : n = 1 := Nat.eq_one_of_div_two_eq_zero_and_ne_zero hdiv hn
    subst hn1; simp [bitChar]
  · rw [if_neg hdiv]
    have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
    have h_ne_nil : (binaryString (n / 2)).data ≠ [] :=
      binaryString_data_ne_nil (n / 2)
    have h_head_eq : ((binaryString (n / 2)) ++ String.singleton (bitChar (n % 2))).data.head! =
                     (binaryString (n / 2)).data.head! := by
      simp [String.data_append, List.head_append_singleton_of_ne_nil h_ne_nil]
    rw [h_head_eq]
    exact ih (n / 2) hlt hdiv

/-- Either `binaryString n` is `"0"`, or it has positive length and no leading zero. -/
lemma binaryString_no_leading_zero (n : Nat) :
    binaryString n = "0" ∨
    ((binaryString n).data.length > 0 ∧ (binaryString n).data.head! ≠ '0') := by
  by_cases hzero : n = 0
  · subst hzero; left; simp [binaryString]
  · right
    have h_head : (binaryString n).data.head! ≠ '0' :=
      binaryString_data_head_ne_zero n hzero
    have h_len : (binaryString n).data.length > 0 :=
      binaryString_length_pos n
    exact ⟨h_len, h_head⟩

/-- Roundtrip correctness: converting `n` to a binary string and parsing it back recovers `n`. -/
lemma binaryString_correct (n : Nat) : binaryToNat (binaryString n) = n := by
  induction' n using Nat.strong_induction_on with n ih
  unfold binaryString
  by_cases hzero : n = 0
  · subst hzero; simp [binaryToNat, Char.binaryDigitToNat]
  · rw [if_neg hzero]
    by_cases hdiv : n / 2 = 0
    · rw [if_pos hdiv]
      have hn1 : n = 1 := Nat.eq_one_of_div_two_eq_zero_and_ne_zero hdiv hzero
      subst hn1; simp [binaryToNat, bitChar, Char.binaryDigitToNat]
    · rw [if_neg hdiv]
      simp [binaryToNat_append_singleton, bitChar]
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by omega)
      rw [ih (n / 2) hlt]
      by_cases hmod : n % 2 = 0
      · simp [Char.binaryDigitToNat, hmod]; omega
      · have hm1 : n % 2 = 1 := Nat.mod_two_eq_one_of_ne_zero hmod
        simp [Char.binaryDigitToNat, hm1]; omega

/-- For any `b : Nat`, `bitChar b` is either `'0'` or `'1'`. -/
lemma bitChar_is_bit (b : Nat) : bitChar b = '0' ∨ bitChar b = '1' := by
  unfold bitChar
  by_cases h : b = 0
  · simp [h]
  · simp [h]

/-- Every character in the binary string representation of `n` is either `'0'` or `'1'`. -/
lemma binaryString_chars_are_bits (n : Nat) : ∀ c ∈ (binaryString n).data, c = '0' ∨ c = '1' := by
  induction' n using Nat.strong_induction_on with n ih
  unfold binaryString
  by_cases hzero : n = 0
  · subst hzero; simp
  · rw [if_neg hzero]
    by_cases hdiv : n / 2 = 0
    · rw [if_pos hdiv]
      intro c hc
      simp at hc
      subst hc
      exact bitChar_is_bit (n % 2)
    · rw [if_neg hdiv]
      intro c hc
      rw [String.data_append] at hc
      rcases List.mem_append.mp hc with (hc' | hc')
      · exact ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by norm_num)) c hc'
      · simp at hc'
        subst hc'
        exact bitChar_is_bit (n % 2)

/-! ## Parse characters in a given base -/

/-- Parse a list of hex digit characters in the given base (2 ≤ base ≤ 16) as a natural number,
accumulating from most significant digit first. Returns `none` if any character is not a valid
hex digit (via `Char.hexDigitToNat`) or if a digit value is ≥ the base.

This generalizes `decDigitsToNat` (which is the special case `base = 10`).
For example:
* `charsToNatBase ['1', 'A'] 16 = some 26`
* `charsToNatBase ['1', '2', '3'] 10 = some 123`
* `charsToNatBase ['1', 'G'] 16 = none` (invalid hex char)
* `charsToNatBase ['1', 'A'] 10 = none` (digit 10 ≥ base 10) -/
def charsToNatBase (cs : List Char) (base : Nat) (acc : Nat := 0) : Option Nat :=
  match cs with
  | [] => some acc
  | c :: rest =>
    match Char.hexDigitToNat c with
    | some d =>
        if d < base then
          charsToNatBase rest base (acc * base + d)
        else none
    | none => none

/-- Parse a string of digits in the given `base` with custom validation and digit-value
functions. Each character `c` must satisfy `valid c` to be accepted; its numeric value is
computed by `digitVal c`. Uses Horner's method: `foldl (fun acc c => acc * base + digitVal c) 0`,
short-circuiting to `none` on the first invalid character.

This generalizes `charsToNatBase` (which uses the fixed `Char.hexDigitToNat`) and
`decDigitsToNat` (base 10, non-optional). For example:
* `parseDigits "101" 2 (· = '0' ∨ · = '1') (· = '1').toNat` = `some 5`
* `parseDigits "1A" 16 isHexDigit hexDigitVal` (with appropriate helpers)
* `parseDigits "12x3" 10 isDigit decDigitVal` = `none` (contains 'x')

See also `charsToNatBase` for a recursive alternative on `List Char`. -/
def parseDigits (s : String) (base : Nat)
    (valid : Char → Bool) (digitVal : Char → Nat) : Option Nat :=
  (s.data).foldl
    (fun acc c =>
      match acc with
      | none => none
      | some n =>
        if valid c then
          some (n * base + digitVal c)
        else
          none)
    (some 0)

/-- `Char.hexDigitToNat` is the left inverse of `natToHexChar` for digits 0–15. -/

lemma hexDigitToNat_natToHexChar (d : Nat) (hd : d < 16) : Char.hexDigitToNat (natToHexChar d) = some d := by
  unfold natToHexChar Char.hexDigitToNat
  interval_cases d <;> rfl

/-- `charToDigit` is the left inverse of `natToHexChar` for digits 0–15.
    This is the total (Nat-valued) counterpart of `hexDigitToNat_natToHexChar`. -/

lemma charToDigit_natToHexChar (d : Nat) (hd : d < 16) : charToDigit (natToHexChar d) = d := by
  unfold natToHexChar charToDigit
  interval_cases d <;> decide

end String

namespace String

/-! ### `String.mk` from a range-generated list -/

/-- Mapping a function over a `String`'s underlying character list and re-wrapping
via `String.mk` preserves string length: `(String.mk (cs.map f)).length = (String.mk cs).length`.
This is a foundational lemma — `length_map` and `length_mk_map_range` are both consequences
of this fact. -/

lemma length_mk_map (cs : List Char) (f : Char → Char) :
    (String.mk (cs.map f)).length = (String.mk cs).length := by
  dsimp
  rw [List.length_map]

/-- The length of a string built from `List.map f (List.range n)` equals `n`.
This is useful when constructing a string of known length by applying a function
to each index `0..n-1`. -/
lemma length_mk_map_range (f : Nat → Char) (n : Nat) :
    (String.mk (List.map f (List.range n))).length = n := by
  calc
    (String.mk (List.map f (List.range n))).length = (List.map f (List.range n)).length :=
      String.length_mk _
    _ = (List.range n).length := List.length_map _ _
    _ = n := List.length_range n

end String

namespace String

/-! ## `String.mk` / `String.data` conversion -/

/-- The length of `String.mk` applied to a `replicate` list equals the replication count. -/
lemma length_mk_replicate (n : Nat) (c : Char) : (String.mk (List.replicate n c)).length = n := by
  simp

/-- The length of a string built from a head character followed by `k` copies of another
character equals `k + 1`. This generalizes the common pattern where the first character
is special (e.g., a required digit) and the remaining characters are a repeated filler.
For example, `String.mk ('2' :: List.replicate 4 'a')` has length 5. -/
lemma length_mk_cons_replicate (x y : Char) (k : Nat) :
    (String.mk (x :: List.replicate k y)).length = k + 1 := by
  simp

/-- Build a `String` by repeating a character `n` times.
Equivalent to `String.mk (List.replicate n ch)`.
For example, `String.ofReplicate 5 'A' = "AAAAA"`. -/
def ofReplicate (n : Nat) (ch : Char) : String :=
  String.mk (List.replicate n ch)

/-- The length of `String.ofReplicate n c` is `n`. -/

lemma length_ofReplicate (n : Nat) (c : Char) : (ofReplicate n c).length = n :=
  length_mk_replicate n c

/-- If a character `d` is in the data of `String.ofReplicate n c`, then `d = c`.
This is a key lemma for reasoning about character membership in repeated-character
strings — every character in the result is exactly the replicated character. -/
lemma mem_ofReplicate_data (n : Nat) (c d : Char) (h : d ∈ (ofReplicate n c).data) : d = c := by
  unfold ofReplicate at h
  have h' : d ∈ List.replicate n c := by simpa using h
  rcases List.mem_replicate.mp h' with ⟨_, h_eq⟩
  exact h_eq

/-- If a predicate `p` holds for character `c`, then it holds for every character in
`String.ofReplicate n c`. This generalizes patterns where a property of the replicated
character propagates to all characters in the resulting string (e.g., hex digit
validation, all-digits checks). -/
lemma forall_mem_ofReplicate_data_of_pred {p : Char → Bool} (n : Nat) (c : Char)
    (hc : p c = true) : ∀ d, d ∈ (ofReplicate n c).data → p d = true := by
  intro d hd
  rcases mem_ofReplicate_data n c d hd with rfl
  exact hc

/-- `String.mk` distributes over list concatenation:
constructing a string from concatenated character lists is the same as
concatenating the strings built from each list individually. -/
lemma mk_append (l1 l2 : List Char) : String.mk (l1 ++ l2) = String.mk l1 ++ String.mk l2 := by
  calc
    String.mk (l1 ++ l2) = String.mk (((String.mk l1).data) ++ ((String.mk l2).data)) := by simp
    _ = String.mk l1 ++ String.mk l2 := by rw [String.congr_append]

/-- Decompose `String.mk` on a cons cell:
`String.mk (c :: cs) = String.singleton c ++ String.mk cs`.
This is the single-character special case of `mk_append`. -/
lemma mk_cons (c : Char) (cs : List Char) : String.mk (c :: cs) = String.singleton c ++ String.mk cs := by
  apply String.ext; simp

/-- Converting a list of characters to a `String` via `.asString` and then extracting
the data recovers the original list. This is a convenient `@[simp]` lemma that avoids
the need to unfold `List.asString` (which is `String.mk`). -/
lemma asString_data (l : List Char) : l.asString.data = l := rfl

/-- Reconstructing a string from its own data recovers the original string.
This is the converse of `asString_data`: while `asString_data` says
`(String.mk l).data = l`, this lemma says `String.mk s.data = s`.
Together they establish that `String.mk` and `String.data` are inverses. -/
lemma mk_data (s : String) : String.mk s.data = s := by
  simpa [List.asString] using String.asString_data (b := s)

/-- Converting a list of characters to a `String` via `String.mk` and then extracting
the list via `.toList` recovers the original list. Also works with `List.asString` since
`.asString` is `String.mk`. This is the `.toList` counterpart of `asString_data`. -/
lemma toList_mk (l : List Char) : (String.mk l).toList = l := by
  simp

/-- The `.data` of a string built by folding `String.push` over a list of characters
is the `.data` of the initial string concatenated with the character list.
This is a key lemma for reasoning about string construction via `foldl`.
For example: `("".foldl (fun s c => s.push c) ['a','b']).data = ['a','b']`. -/
lemma data_foldl_push (init : String) (cs : List Char) :
    (cs.foldl (fun s c => s.push c) init).data = init.data ++ cs := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih =>
    simp [ih, List.append_assoc]

/-- Mapping `Char.toLower` over a string's character data yields the same result
as lowering the string and then getting its data. Useful for reasoning about
case-insensitive string operations. -/
lemma map_toLower_eq_toLower_data (s : String) : List.map Char.toLower s.data = s.toLower.data := by
  calc
    List.map Char.toLower s.data = ({ data := List.map Char.toLower s.data } : String).data := rfl
    _ = (String.map Char.toLower s).data := by rw [String.map_eq]
    _ = s.toLower.data := rfl

/-- `String.toLower` is idempotent: lowering a string twice has no additional effect.
`String.toLower (String.toLower s) = String.toLower s` for all strings `s`.
This follows from the idempotence of `Char.toLower` (see `Char.toLower_idem`). -/
lemma toLower_idem (s : String) : String.toLower (String.toLower s) = String.toLower s := by
  simp [String.toLower, String.map_eq, List.map_map, Function.comp, Char.toLower_idem]

/-- Mapping a character function over a string preserves its length:
`(s.map f).length = s.length`. This follows from `String.map` being implemented
as `String.mk (List.map f s.data)`. -/

lemma length_map (f : Char → Char) (s : String) : (s.map f).length = s.length := by
  rw [String.map_eq]; simp

/-- `String.map` distributes over `.data` in the expected way:
the character data of a mapped string is the mapped character data of the original. -/

lemma map_data_eq (s : String) (f : Char → Char) : (s.map f).data = (s.data).map f := by
  simp [String.map_eq]

/-- Character `c` is in the data of `s.map f` iff there exists a character `c'`
in the data of `s` such that `f c' = c`. This is the `String`-level version of
`List.mem_map`, factoring through `map_data_eq`. -/
lemma mem_map_data_iff (s : String) (f : Char → Char) (c : Char) :
    c ∈ (s.map f).data ↔ ∃ c' ∈ s.data, f c' = c := by
  rw [map_data_eq, List.mem_map]

/-! ### Mapping characters to a list of any type -/

/-- Map a function `f : Char → α` over each character of a string, collecting
the results in a `List α`. Unlike `String.map` which stays within `String` (since
the codomain is `Char`), `mapToList` works for any target type `α`.
For example, `"abc".mapToList Char.toNat = [97, 98, 99]`. -/
def mapToList {α : Type} (f : Char → α) (s : String) : List α :=
  s.toList.map f

/-- Mapping a function over a string's characters via `mapToList` preserves length:
the resulting list has exactly as many elements as the original string has characters.
For example, `("abc".mapToList Char.toNat).length = 3 = "abc".length`. -/

lemma length_mapToList {α : Type} (f : Char → α) (s : String) : (mapToList f s).length = s.length := by
  simp [mapToList]

/-- Mapping `String.mk` then `String.data` over a list of character lists is the identity.
In other words, `String.mk` and `String.data` are inverses when lifted to lists. -/
lemma map_mk_data_eq_map_id (xs : List (List Char)) : (xs.map String.mk).map String.data = xs := by
  have h : String.data ∘ (@String.mk) = (id : List Char → List Char) := by
    funext cs; rfl
  simp [h]

/-- Mapping `String.mk` over the reverse of a list of strings' data
recovers the reverse of the original list. This is a consequence of
`mk_data` (the identity `String.mk ∘ String.data = id`), lifted to lists
via `List.map_reverse` and `List.map_map`. -/
lemma map_mk_data_reverse (ws : List String) :
    List.map String.mk ((ws.map String.data).reverse) = ws.reverse := by
  have h_fun : (String.mk ∘ String.data : String → String) = id := by
    funext s; exact mk_data s
  calc
    List.map String.mk ((ws.map String.data).reverse) = (List.map (String.mk ∘ String.data) ws).reverse := by
      rw [List.map_reverse, List.map_map]
    _ = ws.reverse := by
      rw [h_fun, List.map_id]

/-- If a nonempty list of characters is converted to a `String`, the result is not `""`. -/
lemma string_mk_ne_empty_of_ne_nil {l : List Char} (h : l ≠ []) : String.mk l ≠ "" := by
  intro heq
  have h' : l = [] := by simpa using congrArg String.data heq
  exact h h'

/-- `String.mk l` is the empty string iff the underlying list `l` is empty.
This is a convenient characterization: constructing a string from characters
yields `""` exactly when there are no characters. -/
lemma mk_eq_empty_iff (l : List Char) : String.mk l = "" ↔ l = [] := by
  constructor
  · intro h
    have hdata := congrArg String.data h
    simpa using hdata
  · intro h; subst h; rfl

/-- `String.mk` is injective on `List Char`. This follows from `String.data` being a left
inverse: `String.mk` followed by `String.data` recovers the original character list. -/
lemma mk_injective : Function.Injective (String.mk : List Char → String) := by
  intro x y h
  apply_fun String.data at h
  simpa using h

/-- Mapping `String.mk` over a `Nodup` list of character lists preserves `Nodup`.
This is a direct consequence of `mk_injective`. -/
lemma nodup_map_mk (l : List (List Char)) (h : l.Nodup) : (l.map String.mk).Nodup :=
  List.Nodup.map mk_injective h

end String
