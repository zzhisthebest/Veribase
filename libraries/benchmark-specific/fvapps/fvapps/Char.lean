import Mathlib

namespace Specific

open _root_.List

namespace Char

/-! ## Unicode code point bounds

Every valid `Char` has a code point (`toNat`) strictly less than `0x110000 = 1114112`,
the maximum Unicode scalar value. This lemma appears frequently in proofs that enumerate
or filter characters by code point. -/

/-- For any valid Unicode character `c`, its code point `c.toNat` is strictly less than
`1114112` (the maximum Unicode scalar value). -/
theorem toNat_lt_maxUnicode (c : Char) : c.toNat < 1114112 := by
  have hv : c.toNat.isValidChar := by
    simpa using c.valid
  unfold Nat.isValidChar at hv
  rcases hv with (h | h)
  · omega
  · omega

/-! ## `Char.ofNat` / `Char.toNat` inverses

`Char.ofNat_toNat` (the direction `Char.ofNat c.toNat = c`) is already provided by `Init`.
This module adds the reverse direction for valid code points. -/

/-- If `n` is a valid Unicode code point, then `(Char.ofNat n).toNat = n`. -/
theorem toNat_ofNat_of_valid {n : Nat} (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat Char.toNat Char.ofNatAux
  rw [dif_pos h]
  simp [UInt32.toNat_ofNat]

/-- For any `n < 128` (the ASCII range), `(Char.ofNat n).toNat = n`.
This is a convenient corollary of `toNat_ofNat_of_valid` for the common
case of ASCII characters where `n < 128` trivially implies `n.isValidChar`. -/
theorem toNat_ofNat_of_lt_128 {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  apply toNat_ofNat_of_valid
  unfold Nat.isValidChar
  omega

/-- For any `n < 55296` (strictly before the UTF-16 surrogate range starting at U+D800),
`(Char.ofNat n).toNat = n`. This covers the entire Basic Multilingual Plane up to the
surrogate pair range (0xD800–0xDFFF are not valid Unicode scalar values).
A convenient bound for problems dealing with common character ranges. -/
theorem toNat_ofNat_of_lt_55296 {n : Nat} (h : n < 55296) : (Char.ofNat n).toNat = n := by
  apply toNat_ofNat_of_valid
  unfold Nat.isValidChar
  omega

/-! ## Vowel detection

Utilities for identifying vowel characters (a, e, i, o, u), case-insensitively. -/

/-- The set of lowercase vowel characters. -/
def vowels : List Char := ['a', 'e', 'i', 'o', 'u']

/-- Check whether a character is a vowel, case-insensitively. -/
def isVowel (c : Char) : Bool :=
  vowels.contains c.toLower

/-- `isVowel` is case-insensitive: applying it to the lowercase of a character gives
the same result as applying it to the uppercase. -/
theorem isVowel_toLower_eq_toUpper (c : Char) :
    isVowel c.toLower = isVowel c.toUpper := by
  have lower : c.toLower.toLower = c.toUpper.toLower := by
    by_cases hu : 65 ≤ c.toNat ∧ c.toNat ≤ 90
    · have hn : (Char.ofNat (c.toNat + 32)).toNat = c.toNat + 32 :=
        toNat_ofNat_of_lt_128 (by omega)
      simp only [Char.toLower, Char.toUpper]
      simp [hu, hn, show ¬(97 ≤ c.toNat ∧ c.toNat ≤ 122) by omega,
        show ¬(65 ≤ c.toNat + 32 ∧ c.toNat + 32 ≤ 90) by omega]
      omega
    · by_cases hl : 97 ≤ c.toNat ∧ c.toNat ≤ 122
      · have hn : (Char.ofNat (c.toNat - 32)).toNat = c.toNat - 32 :=
          toNat_ofNat_of_lt_128 (by omega)
        simp only [Char.toLower, Char.toUpper]
        simp [hu, hl, hn, show 65 ≤ c.toNat - 32 by omega,
          show c.toNat - 32 ≤ 90 by omega, Nat.sub_add_cancel (show 32 ≤ c.toNat by omega),
          Char.ofNat_toNat]
      · simp [Char.toLower, Char.toUpper, hu, hl]
  simpa only [isVowel] using congrArg (fun x : Char => vowels.contains x) lower

/-! ## Soundex vowel detection

Soundex is a phonetic algorithm that maps names to a four-character code.
It has its own vowel classification, notably treating 'Y' as a vowel. -/

/-- The set of vowel characters used in the Soundex phonetic algorithm.
    Note: Soundex treats 'Y' as a vowel, unlike standard vowel classification. -/
def soundexVowels : List Char := ['A', 'E', 'I', 'O', 'U', 'Y']

/-- Check whether a character is a Soundex vowel (A, E, I, O, U, Y).
    Uses uppercase comparison because Soundex processing typically uppercases input first. -/
def isSoundexVowel (c : Char) : Bool :=
  soundexVowels.contains c

end Char

end Specific
