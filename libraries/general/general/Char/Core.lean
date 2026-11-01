import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Char


/-! ### Lowercase range bounds -/

/--
If a character is between `'a'` and `'z'` inclusive, its numeric code
(`Char.toNat`) lies between 97 and 122 (the ASCII codes for `'a'` and `'z'`).
-/
lemma toNat_range_of_lowercase {ch : Char} (hlo : 'a' ≤ ch) (hhi : ch ≤ 'z') :
    97 ≤ ch.toNat ∧ ch.toNat ≤ 122 := by
  have hlo_val : 'a'.val ≤ ch.val := (Char.le_def.mp hlo)
  have hhi_val : ch.val ≤ 'z'.val := (Char.le_def.mp hhi)
  constructor <;> simpa

/-- For a lowercase letter `c` (between `'a'` and `'z'` inclusive),
the zero-based index `c.toNat - 'a'.toNat` is strictly less than 26. -/
lemma char_index_lt_26 (c : Char) (hc_low : 'a' ≤ c) (hc_high : c ≤ 'z') :
    c.toNat - 'a'.toNat < 26 := by
  have ha_nat : 'a'.toNat = 97 := by decide
  have hz_nat : 'z'.toNat = 122 := by decide
  have h_low : 97 ≤ c.toNat := by
    have h := (Char.le_def.mp hc_low)
    simpa
  have h_high : c.toNat ≤ 122 := by
    have h := (Char.le_def.mp hc_high)
    simpa
  rw [ha_nat]
  omega


  /-- For codepoints below the Unicode surrogate range start (`0xD800`),
  `Char.ofNat` preserves the codepoint under `toNat`. That is,
  `(Char.ofNat n).toNat = n` for all `n < 0xD800`. -/
  lemma toNat_ofNat_of_lt_d800 {n : Nat} (hn : n < 0xd800) :
      (Char.ofNat n).toNat = n := by
    have h : n.isValidChar := Or.inl hn
    simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

  /-- `Char.ofNatAux n h` followed by `Char.toNat` recovers `n`.
  This is the internal version of `toNat_ofNat_of_isValidChar`,
  dealing directly with the `ofNatAux` constructor. -/
  lemma toNat_ofNatAux_of_isValidChar {n : Nat} (h : n.isValidChar) : (Char.ofNatAux n h).toNat = n := by
    simp [Char.ofNatAux, Char.toNat]

  /-- If `n` is a valid Unicode character code point (`n.isValidChar`),
  then `(Char.ofNat n).toNat = n`. This is the general version of
  `toNat_ofNat_of_lt_d800`, covering all valid codepoints, not just
  those below `0xD800`. -/
  lemma toNat_ofNat_of_isValidChar {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
    unfold Char.ofNat
    simp [h, toNat_ofNatAux_of_isValidChar h]

/-! ### ASCII character classification -/

/-- Check whether a character is within the ASCII range (code point ≤ 127).
This is equivalent to `isInRange 0 127 c` and `c.toNat ≤ 127`.
For example, `isAscii 'A' = true`, `isAscii 'é' = false`. -/
def isAscii (c : Char) : Bool :=
  c.toNat ≤ 127

/-- Check if a character's Unicode code point lies within the inclusive range [lo, hi]. -/
def isInRange (lo hi : Nat) (c : Char) : Bool :=
  let n := c.toNat
  lo ≤ n && n ≤ hi

/-- Check if a character is alphanumeric (letter or digit).
This uses the Unicode-aware `Char.isAlpha` and `Char.isDigit` predicates. -/
def isAlphaNum (c : Char) : Bool := c.isAlpha || c.isDigit

/-- Check if a character is alphabetic (letter) or the space character `' '`.
This is narrower than `isAlphanumOrSpace` which also accepts digit characters.
For example:
* `isAlphaOrSpace 'a' = true`
* `isAlphaOrSpace ' ' = true`
* `isAlphaOrSpace '3' = false`
* `isAlphaOrSpace '-' = false` -/
def isAlphaOrSpace (c : Char) : Bool :=
  Char.isAlpha c ∨ c = ' '

/-- Check if a character is alphanumeric or the underscore character `'_'`.
This generalizes the common pattern of testing for valid identifier characters
in product names, variable names, and similar contexts.
For example:
* `isAlphaNumOrUnderscore 'a' = true`
* `isAlphaNumOrUnderscore '3' = true`
* `isAlphaNumOrUnderscore '_' = true`
* `isAlphaNumOrUnderscore '-' = false` -/
def isAlphaNumOrUnderscore (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c = '_'

/-- Check if a character is alphanumeric (letter or digit) or a hyphen `'-'`.
This is the character-level predicate for domain-name validation (RFC 1035:
letters, digits, hyphens), URL slug characters, and similar contexts where
hyphens are allowed but underscores are not.

For example:
* `isAlphaNumOrHyphen 'a' = true`
* `isAlphaNumOrHyphen '3' = true`
* `isAlphaNumOrHyphen '-' = true`
* `isAlphaNumOrHyphen '_' = false`
* `isAlphaNumOrHyphen '!' = false` -/
def isAlphaNumOrHyphen (c : Char) : Bool :=
  (c.isAlpha ∨ c.isDigit) ∨ c = '-'

/-- Check if a character is a valid identifier character: alphanumeric (letter or digit),
hyphen `'-'`, or underscore `'_'`. This is a common pattern for validating usernames,
URL slugs, file names, and other identifier-like strings.

For example:
* `isIdentChar 'a' = true`
* `isIdentChar '3' = true`
* `isIdentChar '-' = true`
* `isIdentChar '_' = true`
* `isIdentChar '!' = false`
* `isIdentChar ' ' = false` -/
def isIdentChar (c : Char) : Bool :=
  (c.isAlpha ∨ c.isDigit) ∨ c = '-' ∨ c = '_'

/-- A character is alphanumeric or a space. Generalizes the common pattern of
checking whether a character is a letter, digit, or whitespace separator.
Uses the built-in `Char.isAlphanum` (Unicode-aware). -/
def isAlphanumOrSpace (c : Char) : Bool :=
  c.isAlphanum || c == ' '

/-- Check if a character is alphanumeric (letter or digit), a space `' '`, or an apostrophe `'\''`.
This is a common predicate for text normalization/cleaning where only letters, digits,
spaces, and apostrophes are kept (e.g., stripping punctuation while preserving contractions).

For example:
* `isAlphaNumOrSpaceOrApostrophe 'a' = true`
* `isAlphaNumOrSpaceOrApostrophe '3' = true`
* `isAlphaNumOrSpaceOrApostrophe ' ' = true`
* `isAlphaNumOrSpaceOrApostrophe '\'' = true`
* `isAlphaNumOrSpaceOrApostrophe '!' = false` -/
def isAlphaNumOrSpaceOrApostrophe (c : Char) : Bool :=
  (c.isAlpha || c.isDigit) || c = ' ' || c = '\''

/-- Check whether a character is alphanumeric (letter or digit) or belongs to any character
in the given `symbols` list. This is the general parameterized form of `isAlphanumOrSpace`,
`isAlphanumOrUnderscore`, and similar predicates — the caller provides the allowed extra symbols.

For example:
* `isAlphanumOrAnyOf ['_', '-'] 'a' = true` (alphanumeric)
* `isAlphanumOrAnyOf ['_', '-'] '_' = true` (in symbols list)
* `isAlphanumOrAnyOf ['_', '-'] '!' = false` (neither alphanumeric nor in list)
* `isAlphanumOrAnyOf [] 'a' = true` (alphanumeric, empty symbols list) -/
def isAlphanumOrAnyOf (symbols : List Char) (c : Char) : Bool :=
  c.isAlphanum || symbols.any (c = ·)

/-- Check whether a character is alphanumeric (letter or digit) or a common filename/path
special character: underscore `'_'`, tilde `'~'`, hyphen `'-'`, backslash `'\\'`, or dot `'.'`.
These are the characters commonly permitted in file names and paths alongside alphanumerics.

For example:
* `isFilenameChar 'a' = true` (letter)
* `isFilenameChar '3' = true` (digit)
* `isFilenameChar '_' = true` (underscore)
* `isFilenameChar '~' = true` (tilde)
* `isFilenameChar '-' = true` (hyphen)
* `isFilenameChar '\\' = true` (backslash)
* `isFilenameChar '.' = true` (dot)
* `isFilenameChar '!' = false` (not in allowed set) -/
def isFilenameChar (c : Char) : Bool :=
  isAlphanumOrAnyOf ['_', '~', '-', '\\', '.'] c

/-- Check if a character is an ASCII lowercase letter ('a' .. 'z'). -/
def isLowerChar (c : Char) : Bool := isInRange 97 122 c

/-- Check if a character is an ASCII uppercase letter ('A' .. 'Z'). -/
def isUpperChar (c : Char) : Bool := isInRange 65 90 c

/-- Check if a character is an ASCII digit ('0' .. '9'). -/
def isDigitChar (c : Char) : Bool := isInRange 48 57 c

/-- Check if a character is an ASCII uppercase letter ('A' .. 'Z') or digit ('0' .. '9').
This is a common pattern for validating identifier characters in alphanumeric
product codes, user IDs, and similar contexts.
For example, `isUpperOrDigit 'X' = true`, `isUpperOrDigit '5' = true`, `isUpperOrDigit 'a' = false`. -/
def isUpperOrDigit (c : Char) : Bool :=
  isUpperChar c || isDigitChar c

/-- Check if a character is a vowel (a, e, i, o, u), case-insensitive.
For example, `isVowel 'A' = true`, `isVowel 'b' = false`, `isVowel 'u' = true`. -/
def isVowel (c : Char) : Bool :=
  match c.toLower with
  | 'a' | 'e' | 'i' | 'o' | 'u' => true
  | _ => false

/-- `isVowel` returns `true` exactly when the lowercased character is one of a, e, i, o, u. -/
theorem isVowel_eq_true_iff (c : Char) :
    isVowel c = true ↔ (c.toLower = 'a' ∨ c.toLower = 'e' ∨ c.toLower = 'i' ∨ c.toLower = 'o' ∨ c.toLower = 'u') := by
  constructor
  · intro h
    dsimp [isVowel] at h
    by_cases ha : c.toLower = 'a'
    · left; exact ha
    · by_cases he : c.toLower = 'e'
      · right; left; exact he
      · by_cases hi : c.toLower = 'i'
        · right; right; left; exact hi
        · by_cases ho : c.toLower = 'o'
          · right; right; right; left; exact ho
          · by_cases hu : c.toLower = 'u'
            · right; right; right; right; exact hu
            · simp [ha, he, hi, ho, hu] at h
  · intro h
    rcases h with (h | h | h | h | h)
    · simp [isVowel, h]
    · simp [isVowel, h]
    · simp [isVowel, h]
    · simp [isVowel, h]
    · simp [isVowel, h]

/-- Check if a character is an ASCII letter (`'A'`–`'Z'` or `'a'`–`'z'`).
For example, `isLetter 'X' = true`, `isLetter '5' = false`. -/
def isLetter (c : Char) : Bool :=
  isLowerChar c || isUpperChar c

/-- Check if a character is a consonant: an ASCII letter that is not a vowel.
For example, `isConsonant 'B' = true`, `isConsonant 'A' = false`, `isConsonant '3' = false`. -/
def isConsonant (c : Char) : Bool :=
  isLetter c && !(isVowel c)

/-- Check if a character is a Unicode alphabetic consonant: a Unicode letter (`Char.isAlpha`)
that is not a vowel (case-insensitive). This is the Unicode-aware version of `isConsonant`
(which uses ASCII-only `isLetter`). Non-alphabetic characters return `false`.
For example, `isAlphaConsonant 'B' = true`, `isAlphaConsonant 'A' = false`,
`isAlphaConsonant '3' = false`, `isAlphaConsonant 'é' = true` (French 'é' is a letter and not a vowel). -/
def isAlphaConsonant (c : Char) : Bool :=
  c.isAlpha && !(isVowel c)

/-- Case-insensitive character equality.
Returns `true` iff `c1` and `c2` have the same lowercase form.
For example, `charEqCI 'a' 'A' = true` and `charEqCI 'a' 'b' = false`. -/
def charEqCI (c1 c2 : Char) : Bool :=
  c1.toLower = c2.toLower

/-- Check if a character's code point falls in the inclusive range [lo, hi],
    where `lo` and `hi` are given as `Char` values (not `Nat` code points).
    For example, `charInRange 'C' 'A' 'Z' = true` and `charInRange '3' 'A' 'Z' = false`. -/
def charInRange (c lo hi : Char) : Bool :=
  let n := c.toNat
  n ≥ lo.toNat && n ≤ hi.toNat

/-- Prop version of `isInRange`: character's code point is in [lo, hi]. -/
def IsInRange (lo hi : Nat) (c : Char) : Prop :=
  let n := c.toNat
  lo ≤ n ∧ n ≤ hi

/-- Prop version of `charInRange`: character `c` lies in the inclusive
range `[lo, hi]` of `Char` values, compared by `Char.toNat`. -/
def IsInCharRange (lo hi : Char) (c : Char) : Prop :=
  Char.toNat lo ≤ Char.toNat c ∧ Char.toNat c ≤ Char.toNat hi

/-- Equivalence between the Bool `charInRange` and the Prop `IsInCharRange`. -/
lemma charInRange_iff (c lo hi : Char) : charInRange c lo hi ↔ IsInCharRange lo hi c := by
  unfold charInRange IsInCharRange
  simp

/-- Prop: character is an ASCII lowercase letter. -/
def IsLower (c : Char) : Prop := IsInRange 97 122 c

/-- Prop: character is an ASCII uppercase letter. -/
def IsUpper (c : Char) : Prop := IsInRange 65 90 c

/-- Prop: character is an ASCII digit. -/
def IsDigit (c : Char) : Prop := IsInRange 48 57 c

/-- Equivalence between the Bool and Prop versions of ASCII digit check. -/
lemma isDigitChar_iff (c : Char) : isDigitChar c ↔ IsDigit c := by
  unfold isDigitChar IsDigit isInRange IsInRange
  simp

/-! ### ASCII digit or uppercase (Prop) -/

/-- A `Nat` is an ASCII digit code (48–57) or uppercase letter code (65–90),
i.e. its codepoint corresponds to a decimal digit or capital Latin letter. -/
def IsDigitOrUpperCode (n : Nat) : Prop :=
  ('0'.toNat ≤ n ∧ n ≤ '9'.toNat) ∨ ('A'.toNat ≤ n ∧ n ≤ 'Z'.toNat)

/-- `Prop` version: a character is an ASCII digit (`'0'`–`'9'`) or uppercase letter (`'A'`–`'Z'`).
This is the `Prop` counterpart to `isUpperOrDigit`. -/
def IsDigitOrUpper (c : Char) : Prop :=
  IsDigit c ∨ IsUpper c



/-! ### `isAlphanum` decomposition -/

/-- If a character is alphanumeric (`c.isAlphanum`), then it is either alphabetic or a digit.
This follows from the definition of `isAlphanum` as `isAlpha || isDigit`. -/
lemma isAlphanum_imp_isAlpha_or_isDigit (c : Char) (h : c.isAlphanum) : c.isAlpha ∨ c.isDigit := by
  have h_or : (c.isAlpha || c.isDigit) = true := h
  rcases Bool.or_eq_true_iff.mp h_or with (hα | hδ)
  · exact .inl hα
  · exact .inr hδ

/-! ### `isAlpha` decomposition -/

/-- If a character is alphabetic (`c.isAlpha`), then it is either uppercase or lowercase.
This follows from the definition of `isAlpha` as `isUpper || isLower`. -/
lemma isAlpha_imp_isUpper_or_isLower {c : Char} (h : Char.isAlpha c) : c.isUpper ∨ c.isLower := by
  simpa [Char.isAlpha] using h



/-! ### Punctuation classification -/

/-- Check whether a character is an ASCII punctuation symbol.
Recognizes: `. , ! ? ; : ' " ( ) [ ] { } - _`.
Returns `false` for all other characters (letters, digits, whitespace, etc.).

This is useful for string normalization tasks where punctuation should be
replaced with spaces (e.g., tokenization, sentence splitting).

For example:
* `isPunct '!' = true`
* `isPunct '.' = true`
* `isPunct 'a' = false`
* `isPunct ' ' = false` -/
def isPunct (c : Char) : Bool :=
  match c with
  | '.' | ',' | '!' | '?' | ';' | ':' | '\'' | '\"' | '(' | ')' | '[' | ']' | '{' | '}' | '-' | '_' => true
  | _ => false

/-- Check whether a character is a word delimiter: whitespace or core punctuation
(space, newline, tab, comma, period, exclamation, question, semicolon, colon).
Returns `false` for other characters (letters, digits, etc.).

This is useful for word tokenization: splitting a string on any delimiter
character yields the list of words.

For example:
* `isWordDelimiter ' ' = true`
* `isWordDelimiter ',' = true`
* `isWordDelimiter 'a' = false`
* `isWordDelimiter '3' = false` -/
def isWordDelimiter (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == ',' || c == '.' || c == '!' || c == '?' || c == ';' || c == ':'

/-- Characters that separate words in camelCase-style splitting:
space, underscore, and hyphen. This is a more focused predicate than
`isWordDelimiter`, covering only the three most common separators
in identifier-style naming conventions.

For example:
* `wordSeparator ' ' = true`
* `wordSeparator '_' = true`
* `wordSeparator '-' = true`
* `wordSeparator 'a' = false` -/
def wordSeparator (c : Char) : Bool :=
  decide (c = ' ' ∨ c = '_' ∨ c = '-')


end Char

namespace Char


/-! ### Character order monotonicity -/

/-- `Char.toNat` is monotone: if `a ≤ b` as characters, then `Char.toNat a ≤ Char.toNat b`.
This connects the `Char` partial order (defined via `UInt32` / `BitVec 32` comparison)
to the natural number ordering of their Unicode code points. -/
lemma toNat_le_toNat (a b : Char) (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rw [Char.le_def] at h
  rw [UInt32.le_def] at h
  rw [BitVec.le_def] at h
  simpa using h

/-- Character ordering `a ≤ b` is equivalent to the natural number ordering of their
Unicode code points. This provides the full `↔` version of `toNat_le_toNat`. -/
lemma char_le_iff_toNat_le {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat, Char.toNat]



/-! ### Case conversion and ASCII bounds -/

/-- If `Char.isUpper c` holds, then `c.toNat ≤ 90` (the ASCII code for `'Z'`).
This provides an upper bound for uppercase character codes. -/
lemma isUpper_implies_toNat_le_90 (c : Char) (h : Char.isUpper c) : c.toNat ≤ 90 := by
  unfold Char.isUpper at h
  have ⟨_, h90⟩ := Bool.and_eq_true_iff.mp h
  have h90' : c.val ≤ (90 : UInt32) := of_decide_eq_true h90
  simpa using h90'

/-- If `Char.isUpper c` holds, then `65 ≤ c.toNat` (the ASCII code for `'A'`).
This provides a lower bound for uppercase character codes. -/
lemma isUpper_implies_65_le_toNat (c : Char) (h : Char.isUpper c) : 65 ≤ c.toNat := by
  unfold Char.isUpper at h
  have ⟨h65, _⟩ := Bool.and_eq_true_iff.mp h
  have h65' : (65 : UInt32) ≤ c.val := of_decide_eq_true h65
  simpa using h65'

/-- If `Char.isLower c` holds, then `97 ≤ c.toNat` (the ASCII code for `'a'`).
This provides a lower bound for lowercase character codes. -/
lemma isLower_implies_97_le_toNat (c : Char) (h : Char.isLower c) : 97 ≤ c.toNat := by
  unfold Char.isLower at h
  have ⟨h97, _⟩ := Bool.and_eq_true_iff.mp h
  have h97' : (97 : UInt32) ≤ c.val := of_decide_eq_true h97
  simpa using h97'

/-- If `Char.isLower c` holds, then `c.toNat ≤ 122` (the ASCII code for `'z'`).
This provides an upper bound for lowercase character codes. -/
lemma isLower_implies_toNat_le_122 (c : Char) (h : Char.isLower c) : c.toNat ≤ 122 := by
  unfold Char.isLower at h
  have ⟨_, h122⟩ := Bool.and_eq_true_iff.mp h
  have h122' : c.val ≤ (122 : UInt32) := of_decide_eq_true h122
  simpa using h122'

/-- If a character is alphabetic, its Unicode code point is less than 128.
This follows from the ASCII bounds for uppercase (≤ 90) and lowercase (≤ 122) letters. -/
lemma isAlpha_implies_toNat_lt_128 (c : Char) (h : Char.isAlpha c) : c.toNat < 128 := by
  unfold Char.isAlpha at h
  rcases Bool.or_eq_true_iff.mp h with (h_up | h_lo)
  · have hle : c.toNat ≤ 90 := isUpper_implies_toNat_le_90 c h_up
    omega
  · have hle : c.toNat ≤ 122 := isLower_implies_toNat_le_122 c h_lo
    omega

/-- `Char.toLower` is the identity on characters that are already lowercase.
If `c.isLower`, then `Char.toLower c = c`. -/
lemma toLower_eq_self_of_isLower (c : Char) (h : Char.isLower c) : Char.toLower c = c := by
  have h97 : 97 ≤ c.toNat := isLower_implies_97_le_toNat c h
  unfold Char.toLower
  simp
  omega

/-- `Char.toLower` is idempotent: lowering a character twice has no additional effect.
`Char.toLower (Char.toLower c) = Char.toLower c` for all characters `c`.
This holds even for non-alphabetic characters (which are unchanged by `toLower`). -/
lemma toLower_idem (c : Char) : Char.toLower (Char.toLower c) = Char.toLower c := by
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have hn : (Char.ofNat (c.toNat + 32)).toNat = c.toNat + 32 :=
      toNat_ofNat_of_lt_d800 (by omega)
    simp only [Char.toLower, if_pos h, hn]
    rw [if_neg (by omega)]
  · simp [Char.toLower, h]

/-- `Char.toUpper` is idempotent: uppercasing a character twice has no additional effect.
`Char.toUpper (Char.toUpper c) = Char.toUpper c` for all characters `c`.
This holds even for non-alphabetic characters (which are unchanged by `toUpper`). -/
lemma toUpper_idem (c : Char) : Char.toUpper (Char.toUpper c) = Char.toUpper c := by
  by_cases h : 97 ≤ c.toNat ∧ c.toNat ≤ 122
  · have hn : (Char.ofNat (c.toNat - 32)).toNat = c.toNat - 32 :=
      toNat_ofNat_of_lt_d800 (by omega)
    simp only [Char.toUpper, if_pos h, hn]
    rw [if_neg (by omega)]
  · simp [Char.toUpper, h]

/-- If a character `c` is a lowercase ASCII letter (`'a' ≤ c` and `c ≤ 'z'`),
then `c.toUpper` is an uppercase ASCII letter (`'A' ≤ c.toUpper` and `c.toUpper ≤ 'Z'`).
This is the fundamental correctness lemma for `Char.toUpper` on lowercase letters. -/
lemma toUpper_range_of_lowercase (c : Char) (hlo : 'a' ≤ c) (hhi : c ≤ 'z') :
    'A' ≤ c.toUpper ∧ c.toUpper ≤ 'Z' := by
  have h_bounds : 97 ≤ c.toNat ∧ c.toNat ≤ 122 := toNat_range_of_lowercase hlo hhi
  rcases h_bounds with ⟨hlo', hhi'⟩
  have h_toUpper : c.toUpper = Char.ofNat (c.toNat - 32) := by
    unfold Char.toUpper
    have hcond : c.toNat ≥ 97 ∧ c.toNat ≤ 122 := ⟨hlo', hhi'⟩
    simp [hcond]
  rw [h_toUpper]
  have h_sub_lo : 65 ≤ c.toNat - 32 := by omega
  have h_sub_hi : c.toNat - 32 ≤ 90 := by omega
  have h_lt_d800 : c.toNat - 32 < 0xd800 := by omega
  have h_toNat_eq : (Char.ofNat (c.toNat - 32)).toNat = c.toNat - 32 :=
    toNat_ofNat_of_lt_d800 h_lt_d800
  have hA_toNat : 'A'.toNat = 65 := by decide
  have hZ_toNat : 'Z'.toNat = 90 := by decide
  constructor
  · rw [char_le_iff_toNat_le, hA_toNat, h_toNat_eq]
    omega
  · rw [char_le_iff_toNat_le, hZ_toNat, h_toNat_eq]
    omega

/-- If a character is lowercase, applying `toLower` again keeps it lowercase.
This follows from `toLower_eq_self_of_isLower`. -/
lemma isLower_toLower_of_isLower (c : Char) (h : Char.isLower c) : Char.isLower (Char.toLower c) := by
  rw [toLower_eq_self_of_isLower c h]
  exact h

/-- If a character is alphabetic (letter), then its lowercase form `Char.toLower c`
is a lowercase character. This is a fundamental property of case conversion:
uppercase letters become lowercase, lowercase letters stay lowercase. -/
lemma isAlpha_implies_isLower_toLower (c : Char) (h : Char.isAlpha c) : Char.isLower (Char.toLower c) := by
  unfold Char.isAlpha at h
  rcases Bool.or_eq_true_iff.mp h with (h_upper | h_lower)
  · -- uppercase case: Char.toLower c = Char.ofNat (c.toNat + 32)
    have hle : c.toNat ≤ 90 := isUpper_implies_toNat_le_90 c h_upper
    have hge : 65 ≤ c.toNat := isUpper_implies_65_le_toNat c h_upper
    have hsum_le : c.toNat + 32 ≤ 122 := by omega
    have hsum_ge : 97 ≤ c.toNat + 32 := by omega
    have hlt : c.toNat + 32 < 128 := by omega
    have htolower : Char.toLower c = Char.ofNat (c.toNat + 32) := by
      unfold Char.toLower
      simp [hge, hle]
    rw [htolower]
    unfold Char.isLower
    let v97 : Fin 128 := ⟨97, by omega⟩
    let v122 : Fin 128 := ⟨122, by omega⟩
    let v_sum : Fin 128 := ⟨c.toNat + 32, hlt⟩
    have h97val : (97 : UInt32) = UInt32.ofNat (v97 : ℕ) := rfl
    have h122val : (122 : UInt32) = UInt32.ofNat (v122 : ℕ) := rfl
    have hsumval : (Char.ofNat (c.toNat + 32)).val = UInt32.ofNat (v_sum : ℕ) := by
      have : ∀ (n : Fin 128), (Char.ofNat n.val).val = UInt32.ofNat n.val := by decide
      simpa using this v_sum
    rw [h97val, h122val, hsumval]
    have hle1 : (UInt32.ofNat v97.val) ≤ (UInt32.ofNat v_sum.val) := by
      have : ∀ (n m : Fin 128), (UInt32.ofNat n.val) ≤ (UInt32.ofNat m.val) ↔ n.val ≤ m.val := by
        decide
      exact ((this v97 v_sum).mpr hsum_ge)
    have hle2 : (UInt32.ofNat v_sum.val) ≤ (UInt32.ofNat v122.val) := by
      have : ∀ (n m : Fin 128), (UInt32.ofNat n.val) ≤ (UInt32.ofNat m.val) ↔ n.val ≤ m.val := by
        decide
      exact ((this v_sum v122).mpr hsum_le)
    simp [hle1, hle2]
  · exact isLower_toLower_of_isLower c h_lower

/-- If a character is alphabetic, then its lowercase form is never equal to
a non-lowercase separator character. For example, `Char.toLower 'A' ≠ '_'`. -/
lemma toLower_ne_of_not_isLower (c : Char) (hc : Char.isAlpha c) (sep : Char) (hsep : ¬ Char.isLower sep) :
    Char.toLower c ≠ sep := by
  have h_lower : Char.isLower (Char.toLower c) := isAlpha_implies_isLower_toLower c hc
  intro h_eq
  apply hsep
  rw [← h_eq]
  exact h_lower



/-! ### Uppercase conversion (lowercase → uppercase only) -/

/-- Title case: uppercase the first character after lowercasing.
Useful as a building block for word-capitalization routines:
first lowercases the character (so "HELLO" → "hello"), then uppercases it
(so "h" → "H" for the target character).

For example:
* `toTitleCase 'h' = 'H'`
* `toTitleCase 'H' = 'H'` (lowered then uppercased)
* `toTitleCase '5' = '5'` (non-letter unchanged by lower/upper)
* `toTitleCase 'a' = 'A'` -/
def toTitleCase (c : Char) : Char :=
  Char.toUpper (Char.toLower c)

/-- Map a single character: if it is lowercase, convert to uppercase; otherwise leave unchanged.
This differs from `Char.toUpper` in that it only acts on lowercase characters — non-lowercase
characters that nevertheless have uppercase forms (e.g., titlecase variants) are left alone.

For example:
* `toUpperLower 'a' = 'A'`
* `toUpperLower 'Z' = 'Z'`
* `toUpperLower '5' = '5'` -/
def toUpperLower (c : Char) : Char :=
  if c.isLower then c.toUpper else c

/-- If a character is lowercase, `toUpperLower` converts it to uppercase. -/

lemma toUpperLower_of_isLower (c : Char) (h : c.isLower) : toUpperLower c = c.toUpper := by
  simp [toUpperLower, h]

/-- If a character is not lowercase, `toUpperLower` leaves it unchanged. -/

lemma toUpperLower_of_not_isLower (c : Char) (h : ¬ c.isLower) : toUpperLower c = c := by
  simp [toUpperLower, h]



/-! ### Case toggling -/

/-- Toggle the case of an alphabetic character: lowercase becomes uppercase,
    uppercase becomes lowercase.  Non‑alphabetic characters are returned unchanged. -/
def toggleCase (c : Char) : Char :=
  if c.isAlpha then
    if c.isLower then c.toUpper else c.toLower
  else
    c

/-- `toggleCase` leaves non‑alphabetic characters unchanged. -/

lemma toggleCase_nonAlpha (c : Char) (h : ¬ c.isAlpha) : toggleCase c = c := by
  unfold toggleCase
  simp [h]

/-- For an alphabetic character, `toggleCase` applies `toUpper` when lowercase
    and `toLower` otherwise (i.e. when uppercase). -/
lemma toggleCase_isAlpha (c : Char) (h : c.isAlpha) :
    toggleCase c = if c.isLower then c.toUpper else c.toLower := by
  unfold toggleCase
  simp [h]


end Char

namespace Char


/-! ### Alphabet position -/

/-- Position of a letter in the alphabet, case-insensitive:
    a/A=1, b/B=2, …, z/Z=26. Non-letter characters (including digits) map to 0. -/
def charPos (c : Char) : Nat :=
  let n := c.toNat
  if 'a'.toNat ≤ n && n ≤ 'z'.toNat then n - 'a'.toNat + 1
  else if 'A'.toNat ≤ n && n ≤ 'Z'.toNat then n - 'A'.toNat + 1
  else 0

/-- Zero-based alphabet position of an alphabetic character, using Unicode-aware
    character classification (`isAlpha`/`isUpper`). Returns `some n` with `0 ≤ n < 26`
    where `'A'`/`'a'` map to `0`, …, `'Z'`/`'z'` map to `25`.
    Returns `none` for non-alphabetic characters.

    This differs from `charPos` in three ways:
    1. This function is zero-based (A/a = 0), while `charPos` is one-based (A/a = 1).
    2. This function returns `Option Nat` (with `none` for non-letters),
       while `charPos` returns `Nat` (with `0` for non-letters).
    3. This function uses Unicode-aware `isAlpha`/`isUpper` for classification,
       while `charPos` uses ASCII-code-range checks. -/
def charAlphabetPos? (c : Char) : Option Nat :=
  if c.isAlpha then
    if c.isUpper then some (c.toNat - 'A'.toNat)
    else some (c.toNat - 'a'.toNat)
  else none

/-- Zero-based offset of `c` from `base` in Unicode code-point space.
    For example, `charOffset 'a' 'c' = 2`, `charOffset '0' '5' = 5`.
    Callers must ensure `c ≥ base` for meaningful results; the operation is
    mathematically well-defined even for arbitrary characters. -/
def charOffset (base : Char) (c : Char) : Nat :=
  c.toNat - base.toNat

/-- Bracket-pair classifier for balanced bracket validation.
Openers `(`, `[`, `{` return `none` (push). Closers return the expected opener.
Other characters return `none` (ignored). -/
def bracketPair : Char → Option Char
  | '(' => none
  | '[' => none
  | '{' => none
  | ')' => some '('
  | ']' => some '['
  | '}' => some '{'
  | _ => none

/-- Check whether character `c` is one of the standard arithmetic operators (`+`, `-`, `*`).
Generalizes the common pattern of testing for operators in expression parsing
and evaluation problems. -/
def isArithOp (c : Char) : Bool :=
  c == '+' ∨ c == '-' ∨ c == '*'

/-- Precedence level of an arithmetic operator character.
`+` and `-` have precedence 1 (lowest), `*` and `/` have precedence 2.
All other characters have precedence 0.
Useful for expression parsing algorithms such as the shunting‑yard algorithm.

For example:
* `arithPrecedence '+' = 1`
* `arithPrecedence '-' = 1`
* `arithPrecedence '*' = 2`
* `arithPrecedence '/' = 2`
* `arithPrecedence 'a' = 0` -/
def arithPrecedence (c : Char) : Nat :=
  match c with
  | '+' => 1
  | '-' => 1
  | '*' => 2
  | '/' => 2
  | _   => 0

/-- Check whether a character is an ASCII whitespace character:
space (`' '`), tab (`'\t'`), newline (`'\n'`), or carriage return (`'\r'`).
This is useful in string parsing for skipping ASCII whitespace.
For a Unicode-aware whitespace check that also covers characters like
non-breaking space, line separator, etc., see `Char.isWhitespace`. -/
def isSpace (c : Char) : Bool :=
  c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

/-- Check whether character `c` belongs to the list `chars`.
This is the `Bool`-valued version of `c ∈ chars`.
For example, `isElemOf 'a' ['a', 'e', 'i'] = true`. -/
def isElemOf (c : Char) (chars : List Char) : Bool :=
  chars.any (fun v => c == v)


/-! ### Character shifting (Caesar cipher) -/

/-- Shift a character `c` within the range `[base, base+size-1]` by `n` positions,
wrapping around. For example:
* `shiftInRange 'a' 26 'a' 1 = 'b'`
* `shiftInRange 'a' 26 'z' 2 = 'b'`
* `shiftInRange '0' 10 '9' 1 = '0'` -/
def shiftInRange (base : Char) (size : Nat) (c : Char) (n : Nat) : Char :=
  let idx := ((c.toNat - base.toNat) + n) % size
  Char.ofNat (base.toNat + idx)

/-- Shift a lowercase letter `c` by `n` positions, wrapping around at 'z'.
For example, `shiftLower 'a' 1 = 'b'` and `shiftLower 'z' 2 = 'b'`. -/
def shiftLower (c : Char) (n : Nat) : Char :=
  shiftInRange 'a' 26 c n

/-- A Caesar cipher shift: shifts alphabetic characters (both lowercase and uppercase)
by `n` positions, wrapping around within the alphabet. Non-alphabetic characters are
unchanged. This is the full Caesar cipher that handles both cases in one call.

For example:
* `caesarShift 3 'a' = 'd'`
* `caesarShift 3 'X' = 'A'`
* `caesarShift 3 '!' = '!'`
* `caesarShift 1 'z' = 'a'` -/
def caesarShift (n : Nat) (c : Char) : Char :=
  if ('a' ≤ c) ∧ (c ≤ 'z') then
    shiftInRange 'a' 26 c n
  else if ('A' ≤ c) ∧ (c ≤ 'Z') then
    shiftInRange 'A' 26 c n
  else c

/-- Shift an alphabetic character by `n` positions modulo 26 in the Latin alphabet.
Non-alphabetic characters are returned unchanged. Uses `Int` for the shift amount,
which allows negative shifts (backward rotation). Uses Unicode-aware `isAlpha`/`isUpper`
for classification and `Int.emod` for Euclidean modulo.

This is a more general version of `caesarShift` that supports negative offsets.
For example:
* `shiftCharBy 'a' 1 = 'b'`
* `shiftCharBy 'z' (-2) = 'x'`
* `shiftCharBy 'X' 1 = 'Y'`
* `shiftCharBy '!' 3 = '!'` -/
def shiftCharBy (c : Char) (n : Int) : Char :=
  if c.isAlpha then
    let base : Nat :=
      if c.isUpper then ('A').toNat else ('a').toNat
    let offset : Int := (Int.ofNat c.toNat) - (Int.ofNat base)
    let newOffset : Int := (offset + n).emod 26
    Char.ofNat (base + Int.toNat newOffset)
  else c

/-- Reusable lemma: `shiftCharBy` does nothing for non-alphabetic characters. -/

lemma shiftCharBy_of_not_alpha {c : Char} {n : Int} (h : ¬ c.isAlpha) : shiftCharBy c n = c := by
  unfold shiftCharBy
  simp [h]

/-- Reverse index of a character `c` in an alphabet of `size`, starting from `base`.
The first character (at offset 0 from `base`) maps to `size`, and the last
(at offset `size-1`) maps to `1`. Callers must ensure `c ≥ base` and
`c` lies within the alphabet. -/
def reverseIdxFrom (size : Nat) (base : Char) (c : Char) : Nat :=
  size - (c.toNat - Char.toNat base)


/-! ### Lowercase alphabet list -/

/-- The list of lowercase ASCII letters `['a', 'b', ..., 'z']`.
Constructed by mapping `i ↦ Char.ofNat (97 + i)` over `0..<26`.
For example, `lowerAlphabet.get? 0 = some 'a'` and `lowerAlphabet.get? 25 = some 'z'`. -/
def lowerAlphabet : List Char :=
  (List.range 26).map (fun i => Char.ofNat (97 + i))

/-- A character `c` is a lowercase ASCII letter (`'a' ≤ c ∧ c ≤ 'z'`) iff
there exists an index `i < 26` such that `c = Char.ofNat (97 + i)`.
This is the fundamental characterization of the lowercase Latin alphabet by codepoints. -/
lemma lowercase_iff_exists_index (c : Char) :
    ('a' ≤ c ∧ c ≤ 'z') ↔ ∃ i : ℕ, i < 26 ∧ c = Char.ofNat (97 + i) := by
  constructor
  · intro ⟨hlo, hhi⟩
    have hlo' : 'a'.toNat ≤ c.toNat := (char_le_iff_toNat_le.mp hlo)
    have hhi' : c.toNat ≤ 'z'.toNat := (char_le_iff_toNat_le.mp hhi)
    have ha : 'a'.toNat = 97 := by decide
    have hz : 'z'.toNat = 122 := by decide
    have h_lo : 97 ≤ c.toNat := by simpa [ha] using hlo'
    have h_hi : c.toNat ≤ 122 := by simpa [hz] using hhi'
    set i := c.toNat - 97 with hi_def
    have hi : i < 26 := by omega
    have hc_eq : c = Char.ofNat (97 + i) := by
      calc
        c = Char.ofNat c.toNat := by simp
        _ = Char.ofNat (97 + i) := by
          have : c.toNat = 97 + i := by omega
          rw [this]
    exact ⟨i, hi, hc_eq⟩
  · intro ⟨i, hi, hc_eq⟩
    subst hc_eq
    have h_toNat : (Char.ofNat (97 + i)).toNat = 97 + i := by
      have h_all : ∀ j : ℕ, j < 26 → (Char.ofNat (97 + j)).toNat = 97 + j := by decide
      exact h_all _ hi
    have hz_nat : 'z'.toNat = 122 := by decide
    have ha_nat : 'a'.toNat = 97 := by decide
    have h_le_a : 'a' ≤ Char.ofNat (97 + i) := by
      rw [char_le_iff_toNat_le, ha_nat, h_toNat]
      omega
    have h_le_z : Char.ofNat (97 + i) ≤ 'z' := by
      rw [char_le_iff_toNat_le, hz_nat, h_toNat]
      omega
    exact ⟨h_le_a, h_le_z⟩


end Char

namespace Char

/-! ### `List Char` filtering utilities -/

/-- Filter a list of characters, keeping only alphanumeric ones (letters and digits).
This is the `List Char`-level counterpart of `Char.isAlphaNum`, and the filter-only
companion to `cleanAlpha` (which also lowercases the result).

For example:
* `filterAlphaNum ['a', '1', '!'] = ['a', '1']`
* `filterAlphaNum ['!', '@'] = []`
* `filterAlphaNum [] = []` -/
def filterAlphaNum (l : List Char) : List Char :=
  l.filter Char.isAlphaNum

/-- Filter a list of characters to keep only alphabetic characters (`Char.isAlpha`),
then convert them all to lowercase via `Char.toLower`. Non-alphabetic characters
are silently dropped.

This is the `List Char`-level building block for `String.filterAlphaToLower`
(which applies the same transformation to a string's character data).

For example:
* `cleanAlpha ['A', ' ', 'b', ',', 'C'] = ['a', 'b', 'c']`
* `cleanAlpha [] = []`
* `cleanAlpha ['1','2','3'] = []` -/
def cleanAlpha (l : List Char) : List Char :=
  (l.filter Char.isAlpha).map Char.toLower

/-- Filter a list of characters to keep only alphanumeric characters (`Char.isAlphaNum`),
then convert them all to lowercase via `Char.toLower`. Non-alphanumeric characters
(punctuation, whitespace, etc.) are silently dropped.

This is the `List Char`-level building block for `String.filterAlphaNumToLower`
(which applies the same transformation to a string's character data). It is the
alphanumeric counterpart of `cleanAlpha` (which only keeps alphabetic characters).

For example:
* `cleanAlphaNum ['A', '1', '!', 'b'] = ['a', '1', 'b']`
* `cleanAlphaNum ['!', '@'] = []`
* `cleanAlphaNum [] = []` -/
def cleanAlphaNum (l : List Char) : List Char :=
  (l.filter Char.isAlphaNum).map Char.toLower

/-- Convert all characters in a list to lowercase via `Char.toLower`.
Non-alphabetic characters (digits, punctuation, etc.) are unchanged.
This is a standalone utility for the `List.map Char.toLower` pattern
that appears in `cleanAlpha`, `cleanAlphaNum`, and similar preprocessing.

For example:
* `toLowerAll ['A', '1', 'b', '!'] = ['a', '1', 'b', '!']`
* `toLowerAll [] = []` -/
def toLowerAll (l : List Char) : List Char :=
  l.map Char.toLower

end Char
