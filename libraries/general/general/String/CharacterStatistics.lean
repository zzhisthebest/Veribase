import Mathlib
import general.List.Count
import general.List.IndexedUpdate
import general.String.NumericConversion

namespace String

/-! ## Distinct letters with both case variants -/

/-- `hasBothCaseVariants chars c` is true when both the lowercase and uppercase
variants of `c` are present in `chars`. Non-alphabetic characters return `false`. -/
def hasBothCaseVariants (chars : List Char) (c : Char) : Bool :=
  if c.isAlpha then
    chars.contains c.toLower && chars.contains c.toUpper
  else
    false

/-- Auxiliary traversal for counting letters that occur in both cases. -/
def countBothCaseLettersAux (chars : List Char) (lst : List Char) (seen : List Char) : Nat :=
  match lst with
  | [] => 0
  | c :: cs =>
    let lower := c.toLower
    if hasBothCaseVariants chars c && !(seen.contains lower) then
      1 + countBothCaseLettersAux chars cs (lower :: seen)
    else
      countBothCaseLettersAux chars cs seen

/-- Count the number of distinct letters that appear in both cases in `chars`. -/
def countDistinctBothCaseLetters (chars : List Char) : Nat :=
  countBothCaseLettersAux chars chars []

lemma countDistinctBothCaseLetters_nil :
    countDistinctBothCaseLetters [] = 0 := by
  unfold countDistinctBothCaseLetters countBothCaseLettersAux; rfl


/-! ## Leading character count -/

/-- Count the number of leading characters in `s` that satisfy predicate `p`. -/
def countLeading (p : Char → Bool) (s : String) : Nat :=
  (s.toList.takeWhile p).length



/-! ## Character counting -/

/-- Count the number of distinct characters in a string that appear an odd number of times.
Specialization of `List.oddCountList` for `String`. -/
def oddCount (s : String) : Nat := List.oddCountList s.data

/-- Count the number of distinct characters in a string.
Equivalent to the cardinality of the `Finset` of the string's character data.
For example, `countDistinctChars "aabac" = 3` (distinct: `a`, `b`, `c`). -/
def countDistinctChars (s : String) : Nat :=
  (s.data.toFinset).card

/-- Count how many characters in a string appear exactly once.
Equivalent to `(s.data).countP fun c => s.data.count c = 1`.

For example:
* `countUniqueElems "aabbcd" = 2` (c and d each appear once)
* `countUniqueElems "aaa" = 0` (none appear exactly once) -/
def countUniqueElems (s : String) : Nat :=
  (s.data).countP fun c => s.data.count c = 1

/-- Count occurrences of a character in a string. -/
def countChar (c : Char) (s : String) : Nat :=
  (s.data.filter fun d => d = c).length

/-- Tabulate per-character counts for a list of characters in a string.
Returns a list of `(char, count)` pairs in the order the characters appear in `chars`.
For example, `tabulateCharCounts ['a','b'] "abracadabra" = [('a', 5), ('b', 2)]`. -/
def tabulateCharCounts (chars : List Char) (text : String) : List (Char × Nat) :=
  chars.map (fun v => (v, countChar v text))

/-- The count of any character in a string cannot exceed the string's length. -/
lemma countChar_le_length (c : Char) (s : String) : countChar c s ≤ s.length := by
  unfold countChar
  calc
    (s.data.filter fun d => d = c).length ≤ s.data.length := List.length_filter_le _ _
    _ = s.length := rfl

/-- `countChar c s` equals `List.count c s.data`. -/
lemma countChar_eq_count (c : Char) (s : String) : countChar c s = List.count c s.data := by
  unfold countChar
  simp [List.count, List.countP_eq_length_filter, BEq.beq]

/-- If a character appears in a string, its count is positive. -/
lemma countChar_pos_of_mem (c : Char) (s : String) (hc : c ∈ s.data) : countChar c s > 0 := by
  unfold countChar
  have hmem : c ∈ s.data.filter (fun x => x = c) := by
    apply List.mem_filter.mpr
    exact ⟨hc, by simp⟩
  exact List.length_pos_of_mem hmem

/-- If a character has positive count in a string, it appears in the string's data. -/
lemma mem_of_countChar_pos (c : Char) (s : String) (hc : countChar c s > 0) : c ∈ s.data := by
  unfold countChar at hc
  have hne : s.data.filter (fun x => x = c) ≠ [] := by
    intro heq; rw [heq] at hc; simp at hc
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  have hmem_filter := List.mem_filter.mp hd
  rcases hmem_filter with ⟨hd_mem, hd_eq⟩
  have : d = c := by simpa using hd_eq
  rw [this] at hd_mem
  exact hd_mem

/-- A character has positive count in a string iff it belongs to the string's data. -/
lemma countChar_pos_iff_mem (c : Char) (s : String) : countChar c s > 0 ↔ c ∈ s.data :=
  ⟨mem_of_countChar_pos c s, countChar_pos_of_mem c s⟩

/-- If the built-in `String.count c s > 0`, then `c ∈ s.data`.
This relates `String.count` (built-in) to membership via `foldl_count_pos_imp_mem`. -/
lemma mem_of_string_count_pos (c : Char) (s : String) (h : s.count c > 0) : c ∈ s.data := by
  have h_eq : s.count c = s.data.foldl (fun n d => if d = c then n + 1 else n) 0 := by
    simp [String.count, String.foldl_eq]
  rw [h_eq] at h
  exact List.foldl_count_pos_imp_mem s.data c h

/-- A character has zero count in a string iff it does not appear in the string's data. -/
lemma countChar_eq_zero_iff_not_mem (c : Char) (s : String) : countChar c s = 0 ↔ c ∉ s.data := by
  constructor
  · intro hzero hmem
    have hpos : countChar c s > 0 := countChar_pos_of_mem c s hmem
    omega
  · intro h
    unfold countChar
    have hfilter : s.data.filter (fun d => d = c) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro d hd
        have hne : d ≠ c := by
          intro heq
          apply h
          subst heq
          exact hd
        simp [hne])
    simp [hfilter]

/-- If a character does not appear in a string, its count is zero. -/
lemma countChar_zero_of_not_mem (c : Char) (s : String) (h : c ∉ s.data) : countChar c s = 0 := by
  unfold countChar
  have hfilter : s.data.filter (fun d => d = c) = [] :=
    List.filter_eq_nil_iff.mpr (by
      intro d hd
      have hne : d ≠ c := by
        intro heq
        apply h
        subst heq
        exact hd
      simp [hne])
  simp [hfilter]

/-- Count case-insensitive occurrences of character `c` in string `s`.
Each character `d` in `s` is counted if `d.toLower = c`.
For example, `countCharIgnoreCase 'a' "AbraCadabra" = 5`. -/
def countCharIgnoreCase (c : Char) (s : String) : Nat :=
  (s.data.filter fun d => d.toLower = c).length


lemma countCharIgnoreCase_empty (c : Char) : countCharIgnoreCase c "" = 0 := by
  unfold countCharIgnoreCase; simp

/-- Count the number of `'1'` characters in a binary string. -/
def countOnes (s : String) : Nat := countChar '1' s

/-- Count the number of `'0'` characters in a binary string. -/
def countZeros (s : String) : Nat := countChar '0' s

/-- The count of `'1'` characters in a string cannot exceed the string's length. -/
lemma countOnes_le_length (s : String) : countOnes s ≤ s.length :=
  countChar_le_length '1' s

/-- The count of `'0'` characters in a string cannot exceed the string's length. -/
lemma countZeros_le_length (s : String) : countZeros s ≤ s.length :=
  countChar_le_length '0' s

/-- Check whether character `a` appears an odd number of times in string `s`. -/
def hasOddCount (a : Char) (s : String) : Bool :=
  (countChar a s) % 2 = 1

lemma hasOddCount_empty (a : Char) : hasOddCount a "" = false := by
  unfold hasOddCount countChar; simp

/-- Count characters in a string that satisfy a predicate. -/
def countIf (p : Char → Bool) (s : String) : Nat :=
  List.countP p s.data

/-- Count the total occurrences of a character across a list of strings. -/
def countCharInList (c : Char) (words : List String) : Nat :=
  (words.map (countChar c)).sum

/-- Count how many strings in `words` contain the character `c` (at least once).
Unlike `countCharInList` which counts total occurrences across all strings,
this counts each string at most once — a binary per-string yes/no check.
For example, `countContaining 'a' ["ab", "aa", "bc"] = 2`. -/
def countContaining (c : Char) (words : List String) : Nat :=
  List.countP (fun s : String => c ∈ s.data) words

/-- Filter a list of strings to those that contain a given character.
For example, `filterContaining 'a' ["ab", "de", "ba"] = ["ab", "ba"]`.
This is the filtering companion of `countContaining`. -/
def filterContaining (c : Char) (words : List String) : List String :=
  words.filter (fun s => s.contains c)

/-! ## Character extraction from multiple strings -/

/-- Extract all characters from a list of strings into a single flat list. -/
def allChars (words : List String) : List Char :=
  words.flatMap (fun s => s.data)

lemma not_mem_allChars_iff (c : Char) (words : List String) :
    c ∉ allChars words ↔ ∀ w ∈ words, c ∉ w.data := by
  simp [allChars]

/-- A character is in `allChars words` iff there exists a string in `words`
containing that character. This is the positive version of `not_mem_allChars_iff`. -/
lemma mem_allChars_iff (c : Char) (words : List String) :
    c ∈ allChars words ↔ ∃ w ∈ words, c ∈ w.data := by
  simp [allChars]

/-- Split score: count `c1` in the first `i` characters, `c2` in the rest.
    General combinator useful for problems involving partitioning a string. -/
def splitScore (c1 c2 : Char) (i : Nat) (s : String) : Nat :=
  countChar c1 (s.take i) + countChar c2 (s.drop i)

/-- Test whether a string has equal counts of two given characters.
    Useful for checking balance with respect to any character pair. -/
def balancedStringOf (a b : Char) (t : String) : Bool :=
  countChar a t == countChar b t


lemma balancedStringOf_empty (a b : Char) : balancedStringOf a b "" = true := by
  unfold balancedStringOf countChar; simp



/-! ## Frequency vector -/

/-- Compute a frequency vector for a string, given the alphabet size and a
    character-to-index mapping. Returns a `List Nat` of length `numChars` where
    the i-th entry is the count of characters `c` with `charToIndex c = i`.

    This is useful for problems that compare character distributions (e.g.,
    anagram checks, permutation equivalence, "can break another string"). -/
def frequency (numChars : Nat) (charToIndex : Char → Nat) (s : String) : List Nat :=
  s.data.foldl
    (fun acc c =>
      let idx := charToIndex c
      List.incAt acc idx 1)
    (List.replicate numChars 0)


end String

namespace String

/-! ## Minimum changes to an alternating binary string -/

/-- Compute the minimum number of character changes (flips) needed to make
a binary string alternating. An alternating string is one where adjacent characters
differ, i.e., either `"01010..."` or `"10101..."`.

For example, `minChangesToAlternating "0100" = 1` (change the last `'0'` to `'1'`
to get `"0101"`), and `minChangesToAlternating "1111" = 2` (change to `"0101"` or `"1010"`).

Non-binary characters are treated as mismatches against both patterns, so the result
remains mathematically well-defined (though less meaningful) for arbitrary strings. -/
def minChangesToAlternating (s : String) : Nat :=
  Nat.min (List.alternatingMismatches s.data '0' '1')
          (List.alternatingMismatches s.data '1' '0')

/-! ## Consecutive character runs -/

/-- Compute the length of the longest consecutive run of character `c` in string `s`.
Delegates to `List.maxRun` on the underlying character data. -/
def maxRun (c : Char) (s : String) : Nat :=
  List.maxRun c s.data

/-- The longest run of `'1'` characters in the string `s`. -/
def maxOnes (s : String) : Nat := maxRun '1' s

/-- The longest run of `'0'` characters in the string `s`. -/
def maxZeros (s : String) : Nat := maxRun '0' s

/-- Maximum length of a run of *any* consecutive equal characters in a string.
For example, `longestRun "aaabbc" = 3` (three `'a'`s), `longestRun "abc" = 1`.

This differs from `maxRun c s` which finds runs of a specific character `c`;
`longestRun s` finds the overall maximum run length regardless of character. -/
def longestRun (s : String) : Nat :=
  List.longestConsecutiveRun s.data

end String


namespace String

/-! ## Character access -/

/-- Safe character accessor by `Nat` index: returns the character at index `i` in `s`,
or `default` if `i` is out of bounds. Unlike `String.get`, this does not require
a `Pos` argument and handles out-of-bounds gracefully.
For example:
* `charAt "hello" 0 = 'h'`
* `charAt "hello" 10 = default` -/
def charAt (s : String) (i : Nat) : Char :=
  s.data.getD i default

/-! ## Word boundary detection -/

/-- Detect if position `i` in string `s` is the start of a word,
given a separator character `sep` (default space).
A position is a word start if:
- `i = 0` and the first character is not `sep`, or
- the previous character is `sep` and the current character is not `sep`.

For example:
* `isWordStart "hello world" 0 = true` (starts with non-space)
* `isWordStart "hello world" 6 = true` (after the space at index 5)
* `isWordStart "hello world" 1 = false` (inside a word)
* `isWordStart "  leading" 0 = false` (starts with space) -/
def isWordStart (s : String) (i : Nat) (sep : Char := ' ') : Bool :=
  if i = 0 then (charAt s i ≠ sep)
  else (charAt s (i - 1) = sep) && (charAt s i ≠ sep)

/-- The first character of `String.mk (c :: cs)` via `get?` at position `0` is `some c`.
This is a convenient lemma for reasoning about the first character of a constructed string.
For example, `(String.mk ('1' :: ['0','1'])).get? 0 = some '1'`. -/
lemma get?_zero_mk_cons (c : Char) (cs : List Char) :
    (String.mk (c :: cs)).get? (0 : String.Pos) = some c := by
  simp [String.get?, String.utf8GetAux?]

/-- A non-empty string has a non-empty character data list.
If `1 ≤ s.length`, then `s.data ≠ []`. -/
lemma data_ne_nil_of_one_le_length (s : String) (hpos : 1 ≤ s.length) : s.data ≠ [] := by
  intro h
  have hlen : s.data.length = s.length := rfl
  have hlen0 : s.data.length = 0 := by
    rw [h]; simp
  rw [hlen] at hlen0
  omega

/-- If a string is non-empty (i.e., not `""`), then its underlying character data is non-empty.
This is the direct version of `data_ne_nil_of_one_le_length` that takes `s ≠ ""` as the premise
instead of `1 ≤ s.length`. Equivalent via `length_pos_iff_ne_empty`. -/
lemma data_ne_nil_of_string_ne_empty {s : String} (h : s ≠ "") : s.data ≠ [] := by
  intro h_data_empty
  apply h
  apply String.ext
  simpa using h_data_empty

/-- The length of a non-empty string is positive. -/
lemma length_pos_of_ne_empty (s : String) (h_ne : s ≠ "") : s.length > 0 := by
  by_contra! h
  have h_zero : s.length = 0 := by omega
  unfold String.length at h_zero
  have h_data_empty : s.data = [] := (List.length_eq_zero_iff.mp h_zero)
  have h_empty : s = "" := by
    apply String.ext
    simpa using h_data_empty
  exact h_ne h_empty

/-- If a string has length zero, it is the empty string. -/
lemma eq_empty_of_length_eq_zero (s : String) (h : s.length = 0) : s = "" := by
  have h_data_len : s.data.length = 0 := by simpa [String.length_data] using h
  have h_data_empty : s.data = [] := List.length_eq_zero_iff.mp h_data_len
  exact String.ext h_data_empty

/-- A string has length zero iff it is the empty string.
Combines `eq_empty_of_length_eq_zero` and its converse into a single iff lemma. -/
lemma length_eq_zero_iff (s : String) : s.length = 0 ↔ s = "" := by
  constructor
  · exact eq_empty_of_length_eq_zero s
  · intro h; subst h; rfl

/-- A string is non-empty (i.e., has positive length) iff it is not the empty string.
This is the positive-length companion to `length_eq_zero_iff`. For example,
`"abc".length > 0 ↔ "abc" ≠ ""`. Uses `.mp` to get positivity from non-emptiness
and `.mpr` to get non-emptiness from positivity. -/
lemma length_pos_iff_ne_empty (s : String) : s.length > 0 ↔ s ≠ "" := by
  constructor
  · intro h heq
    rw [heq, String.length_empty] at h
    omega
  · intro h
    by_contra! hle
    have hzero : s.length = 0 := by omega
    have hdata_len : s.data.length = 0 := by simpa using hzero
    have hdata_empty : s.data = [] := List.length_eq_zero_iff.mp hdata_len
    exact h (String.ext hdata_empty)

/-- If `s.data = []` then `s.length = 0`. This is the converse of `eq_empty_of_length_eq_zero`,
giving the forward direction from empty data to zero length. -/
lemma length_eq_zero_of_data_empty (s : String) (h : s.data = []) : s.length = 0 := by
  simpa using congrArg List.length h

/-- For a nonempty string `s`, the first character of `s ++ t` equals the first character of `s`. -/
lemma get_zero_nonempty (s t : String) (h : s.data ≠ []) : (s ++ t).get 0 = s.get 0 := by
  rcases s with ⟨sdata⟩
  cases sdata with
  | nil => exfalso; exact h rfl
  | cons c cs =>
    simp [String.get, String.utf8GetAux, String.append]

end String

namespace String

/-! ## String length utilities -/

/-- Check if a string's length is between `lo` and `hi` (inclusive). -/
def lengthBetween (s : String) (lo hi : Nat) : Bool :=
  s.length ≥ lo && s.length ≤ hi

/-! ## Character predicates -/

/-- Check if a character is a lowercase ASCII letter (a-z). -/
def isLowerChar (c : Char) : Bool :=
  let n := c.toNat
  decide (Char.toNat 'a' ≤ n) && decide (n ≤ Char.toNat 'z')

/-- `IsLowerChar c` holds iff `c` is a lowercase ASCII letter ('a'–'z').
This is the `Prop` version of `isLowerChar`. -/
def IsLowerChar (c : Char) : Prop :=
  Char.toNat c ≥ Char.toNat 'a' ∧ Char.toNat c ≤ Char.toNat 'z'

/-- The list of all lowercase ASCII letters `['a', 'b', ..., 'z']`. -/
def allLowerChars : List Char :=
  (List.range 26).map (fun i => Char.ofNat ('a'.toNat + i))

/-- Check if a character is an uppercase ASCII letter (A-Z). -/
def isUpperChar (c : Char) : Bool :=
  let n := c.toNat
  decide (Char.toNat 'A' ≤ n) && decide (n ≤ Char.toNat 'Z')

/-- `IsUpperChar c` holds iff `c` is an uppercase ASCII letter ('A'–'Z').
This is the `Prop` version of `isUpperChar`. -/
def IsUpperChar (c : Char) : Prop :=
  Char.toNat c ≥ Char.toNat 'A' ∧ Char.toNat c ≤ Char.toNat 'Z'

/-- Check if a character is a vowel (a, e, i, o, u), case-insensitive.
Delegates to `Char.isVowel`. -/
def isVowel (c : Char) : Bool := Char.isVowel c

/-- Count the number of vowels in a string, case-insensitive. -/
def countVowels (s : String) : Nat :=
  countIf isVowel s

/-- Count the number of consonant characters in a string.
Only alphabetic characters that are not vowels are counted as consonants.
Non-letter characters (digits, punctuation, whitespace, etc.) are ignored.
Delegates to `Char.isConsonant`. -/
def countConsonants (s : String) : Nat :=
  countIf Char.isConsonant s

/-- Count the number of Unicode alphabetic consonants in a string: characters that are
alphabetic (`Char.isAlpha`) but not vowels (case-insensitive). This is the Unicode-aware
version of `countConsonants` (which uses ASCII-only `Char.isConsonant`).
Non-alphabetic characters (digits, punctuation, whitespace, etc.) are not counted.
For example, `countAlphaConsonants "BcD3!e" = 3` (B, c, D; the digit `'3'` and `'!'`
are not alphabetic, `'e'` is a vowel). -/
def countAlphaConsonants (s : String) : Nat :=
  countIf Char.isAlphaConsonant s

/-- Count the number of lowercase characters in a string.
Uses `Char.isLower` which covers all Unicode lowercase characters.
For example, `countLowercase "Hello World" = 8`. -/
def countLowercase (s : String) : Nat :=
  countIf Char.isLower s


lemma countLowercase_eq (s : String) : countLowercase s = (s.data.filter Char.isLower).length := by
  simp [countLowercase, countIf, List.countP_eq_length_filter]

/-- Count the number of uppercase characters in a string.
Uses `Char.isUpper` which covers all Unicode uppercase characters.
For example, `countUppercase "Hello World" = 2`. -/
def countUppercase (s : String) : Nat :=
  countIf Char.isUpper s


lemma countUppercase_eq (s : String) : countUppercase s = (s.data.filter Char.isUpper).length := by
  simp [countUppercase, countIf, List.countP_eq_length_filter]

/-- Extract all consonant characters (non-vowels) from a string as a `List Char`.
Uses `isVowel` for case-insensitive vowel detection.
For example, `consonants "Hello" = ['H', 'l', 'l']`. -/
def consonants (s : String) : List Char :=
  s.data.filter (fun c => not (isVowel c))

/-- Check if a string contains at least one vowel (case-insensitive). -/
def hasVowel (s : String) : Bool :=
  s.data.any isVowel

/-- Check if all characters in a string are alphanumeric (letter or digit). -/
def allAlphaNum (s : String) : Bool :=
  s.data.all (fun c => c.isAlpha || c.isDigit)

/-- Check if all characters in a string are alphabetic (letters only).
Returns `true` for the empty string. -/
def allAlpha (s : String) : Bool :=
  s.data.all Char.isAlpha

/-- Check if a string is a nonempty sequence of alphabetic characters (a "word").
Returns `false` for the empty string. Equivalent to `s ≠ "" && allAlpha s`.
For example: `isWord "hello" = true`, `isWord "" = false`, `isWord "a1" = false`. -/
def isWord (s : String) : Bool :=
  s ≠ "" && allAlpha s

/-- Check whether all characters in a string are lowercase.
Uses `Char.isLower` which covers all Unicode lowercase characters. -/
def isAllLower (s : String) : Bool :=
  s.data.all Char.isLower

/-- Check whether all characters in a string are uppercase.
Uses `Char.isUpper` which covers all Unicode uppercase characters. -/
def isAllUpper (s : String) : Bool :=
  s.data.all Char.isUpper

end String


namespace String

/-! ## Group extraction -/

/-- Extract groups of consecutive characters satisfying predicate `p` from a list of
characters `chars`, accumulating the current run into `cur`.

For example:
* `extractGroups (·.isDigit) ['a','1','2','3','b','c','3','4'] "" = ["123", "34"]`
* `extractGroups (·.isDigit) ['1','2','3'] "" = ["123"]`
* `extractGroups (·.isDigit) ['a','b','c'] "" = []` -/
def extractGroups (p : Char → Bool) (chars : List Char) (cur : String) : List String :=
  match chars with
  | [] =>
    if cur.length = 0 then [] else [cur]
  | c :: cs =>
    if p c then
      extractGroups p cs (cur.push c)
    else
      if cur.length = 0 then
        extractGroups p cs ""
      else
        cur :: extractGroups p cs ""

/-- Split a string on non-digit characters, returning consecutive digit groups.
For example, `splitOnNonDigits "a123bc34d" = ["123", "34"]`. -/
def splitOnNonDigits (s : String) : List String :=
  extractGroups (·.isDigit) s.data ""

/-- Split `s` on `delim` and check that we get exactly `n` parts, each satisfying `p`.
Returns `false` if the split yields a different number of parts or any part fails `p`.
Useful for validating delimited-string formats (e.g., IPv4/v6, version strings). -/
def splitCheckN (s : String) (delim : Char) (n : Nat) (p : String → Bool) : Bool :=
  match s.split (fun c => decide (c = delim)) with
  | parts => parts.length = n && parts.all p


end String


namespace String


/-! ## Start and end with predicate -/

/-- Check whether the first character of a string satisfies predicate `p`.
Returns `false` for the empty string.

For example:
* `firstCharSatisfies isVowel "apple" = true`
* `firstCharSatisfies isVowel "banana" = false`
* `firstCharSatisfies isVowel "" = false` -/
def firstCharSatisfies (s : String) (p : Char → Bool) : Bool :=
  match s.data with
  | [] => false
  | c :: _ => p c

/-- Check whether a string starts with a vowel, case-insensitive.
Equivalent to `firstCharSatisfies s isVowel`.
For example, `startsWithVowel "apple" = true` and `startsWithVowel "banana" = false`. -/
def startsWithVowel (s : String) : Bool := firstCharSatisfies s isVowel

/-- Check whether the last character of a string satisfies predicate `p`.
Returns `false` for the empty string.
This is the symmetric counterpart of `firstCharSatisfies`.

For example:
* `lastCharSatisfies isVowel "apple" = true` (ends with 'e')
* `lastCharSatisfies isVowel "banana" = true` (ends with 'a')
* `lastCharSatisfies isVowel "dog" = false` (ends with 'g')
* `lastCharSatisfies isVowel "" = false` -/
def lastCharSatisfies (s : String) (p : Char → Bool) : Bool :=
  match s.data.reverse with
  | [] => false
  | c :: _ => p c

/-- Check whether a string ends with a vowel, case-insensitive.
Equivalent to `lastCharSatisfies s isVowel`.
For example, `endsWithVowel "apple" = true` and `endsWithVowel "dog" = false`. -/
def endsWithVowel (s : String) : Bool := lastCharSatisfies s isVowel

/-- Check whether the first and last characters of a string both satisfy predicate `p`.
Returns `false` for the empty string. For a single-character string, checks just that character.

This generalizes patterns like "starts and ends with a vowel" (`startAndEndWith isVowel s`),
which appear in problems counting strings in a range that begin and end with vowels. -/
def startAndEndWith (p : Char → Bool) (s : String) : Bool :=
  match s.data with
  | [] => false
  | (c₁ :: cs) =>
    match cs.reverse with
    | [] => p c₁
    | (c₂ :: _) => p c₁ && p c₂

/-- A string starts and ends with a vowel (case-insensitive).
Convenience specialization of `startAndEndWith` using `isVowel`. -/
def isVowelString (s : String) : Bool := startAndEndWith isVowel s

/-- Check if a character is a decimal digit (`'0'`..`'9'`). -/
def isDecDigit (c : Char) : Bool := c ≥ '0' && c ≤ '9'

/-- `IsDecDigit c` holds iff `c` is a decimal-digit character ('0'–'9').
This is the `Prop` version of `isDecDigit`. -/
def IsDecDigit (c : Char) : Prop :=
  Char.toNat c ≥ Char.toNat '0' ∧ Char.toNat c ≤ Char.toNat '9'

/-- The list of decimal digit characters `['0','1','2','3','4','5','6','7','8','9']`. -/
def decDigits : List Char := ['0','1','2','3','4','5','6','7','8','9']

/-- Check if a character is an English sentence boundary delimiter:
period (`.`), exclamation mark (`!`), or question mark (`?`).
Useful in text segmentation and NLP-related problems. -/
def isSentenceDelimiter (c : Char) : Bool :=
  c = '.' ∨ c = '!' ∨ c = '?'

/-- Check if a string consists entirely of decimal digit characters (`'0'`..`'9'`).
Returns `true` for the empty string (vacuously all characters are digits).
Uses `Char.isDigit` which recognizes all Unicode digit characters. -/
def isDigitString (s : String) : Bool :=
  s.data.all Char.isDigit

/-- `Prop`-valued predicate: every character in `s` is a digit.
This is the `Prop` version of `isDigitString`, suitable for specification preconditions. -/
def allDigits (s : String) : Prop :=
  ∀ c ∈ s.data, c.isDigit

lemma allDigits_iff_isDigitString (s : String) : allDigits s ↔ isDigitString s := by
  simp [allDigits, isDigitString, List.all_eq_true]

/-- Check if a non-empty string consists entirely of digit characters (Unicode-aware,
using `Char.isDigit`). Returns `false` for the empty string.
For a version that returns `true` for empty strings, see `isDigitString`. -/
def isNonemptyDigitString (s : String) : Bool :=
  s ≠ "" && isDigitString s

/-- Check if a string is a nonempty sequence of ASCII decimal digits (`'0'`–`'9'`)
whose numeric value (parsed via `String.toNat?`) is at most `hi`.
Returns `false` for empty strings, strings containing non-digit characters,
or strings whose numeric value exceeds `hi`.

For example:
* `isDecDigitStringLe 255 "192" = true`
* `isDecDigitStringLe 255 "256" = false` (exceeds limit)
* `isDecDigitStringLe 255 "12x" = false` (contains non-digit)
* `isDecDigitStringLe 255 "" = false` (empty)

This generalizes the IPv4 "decimal octet" pattern (where `hi = 255`).
Use `isNonemptyDigitString` for the Unicode-aware, unbounded version. -/
def isDecDigitStringLe (hi : Nat) (s : String) : Bool :=
  s ≠ "" && s.data.all isDecDigit &&
  match s.toNat? with
  | some n => n ≤ hi
  | none => false

/-- Check whether a string represents a natural number in `[0, hi]` with no leading zeros
(unless the value is exactly `"0"`). Uses `String.toNat?` for parsing, which accepts
Unicode digit characters.

Returns `false` for empty strings, strings with non-digit characters, values exceeding `hi`,
or strings with leading zeros (except `"0"` itself).

For example:
* `isNatSegmentLe "192" 255 = true`   (IPv4 octet)
* `isNatSegmentLe "0" 255 = true`     (zero is allowed)
* `isNatSegmentLe "01" 255 = false`   (leading zero)
* `isNatSegmentLe "256" 255 = false`  (exceeds limit)
* `isNatSegmentLe "12x" 255 = false`  (non-digit)
* `isNatSegmentLe "" 255 = false`     (empty)

This generalizes `isDecDigitStringLe` by adding a no-leading-zero check while using
`String.toNat?` for digit validation (Unicode-aware) instead of `isDecDigit`. -/
def isNatSegmentLe (s : String) (hi : Nat) : Bool :=
  if s = "" then
    false
  else
    match s.toNat? with
    | none => false
    | some n =>
        if n > hi then
          false
        else if s = "0" then
          true
        else
          match s.data with
          | c :: _ => c ≠ '0'
          | [] => false

/-- Check that `s` starts with `pref` and the remainder is a nonempty digit string.
Returns `false` if the remainder after `pref` is empty (even if `pref` itself is a prefix).
For example, `hasPrefixThenDigits "i" "i32" = true` but `hasPrefixThenDigits "i" "i" = false`. -/
def hasPrefixThenDigits (pref : String) (s : String) : Bool :=
  s.take pref.length = pref && isNonemptyDigitString (s.drop pref.length)

/-- Check whether a string does not start with the character `'0'`.
Returns `false` for the empty string (since it has no first character to inspect).
Useful as a precondition for problems that parse numbers from strings without leading zeros. -/
def noLeadingZero (s : String) : Bool :=
  match s.data with
  | [] => false
  | c :: _ => c ≠ '0'

/-- Check whether two characters are the same ASCII letter but in different cases.
In ASCII, the difference between a lowercase letter and its uppercase
counterpart is exactly 32. -/
def isSameLetterDiffCase (c₁ c₂ : Char) : Bool :=
  (c₁.toNat = c₂.toNat + 32) ∨ (c₂.toNat = c₁.toNat + 32)

/-- Check if all characters in a string are lowercase ASCII letters. -/
def allLowercase (s : String) : Bool :=
  (s.toList).all isLowerChar

/-- `Prop`-valued predicate: every character in `s` is a Unicode lowercase character. -/
def allLower (s : String) : Prop :=
  ∀ c ∈ s.data, c.isLower

/-- `Prop`-valued predicate: every character in `s` is an ASCII lowercase letter ('a'–'z').
This is the Prop version of `allLowercase`. Equivalent to `allCharsInRange s 'a' 'z'`. -/
def allAsciiLower (s : String) : Prop :=
  ∀ c ∈ s.data, IsLowerChar c

/-- Predicate that all characters in `s` lie in the range `[minChar, maxChar]` (inclusive).
    Useful for validating that a string uses only characters from a given alphabet. -/
def allCharsInRange (s : String) (minChar maxChar : Char) : Prop :=
  ∀ c ∈ s.data, (minChar ≤ c) ∧ (c ≤ maxChar)

/-- General `Prop`-valued predicate: every character in `s` satisfies `p`.
    This generalizes `allDigits`, `allLower`, and `allCharsInRange`
    to an arbitrary character predicate. For example:
    * `allSatisfy (fun c => c.isDigit) s` is equivalent to `allDigits s`
    * `allSatisfy (fun c => c = 'A' ∨ c = 'B') "AB"` holds, while
      `allSatisfy (fun c => c = 'A' ∨ c = 'B') "ABC"` does not. -/
def allSatisfy (p : Char → Prop) (s : String) : Prop :=
  ∀ c ∈ s.data, p c

/-- Check whether every character in `s` belongs to the list `chars`.
Returns `true` for the empty string (vacuously true). -/
def allCharsIn (s : String) (chars : List Char) : Bool :=
  s.data.all (fun c => chars.any (c == ·))

/-- `allCharsInIgnoreCase s chars` holds when every character in `s`
(converted to lowercase) belongs to the character list `chars`.

This is the `Prop` version of `allCharsIn` with case-insensitive comparison:
each character `c` in `s.data` is lowered before checking membership in `chars`. -/
def allCharsInIgnoreCase (s : String) (chars : List Char) : Prop :=
  List.Forall (fun c => Char.toLower c ∈ chars) s.data

/-! ## Character containment -/

/-- Check whether a string contains a given character.
Uses `List.contains` on the underlying character data. -/
def containsChar (s : String) (c : Char) : Bool :=
  s.data.contains c

/-- Returns `true` if `s` contains any character satisfying predicate `p`.
Generalizes `containsChar`: `containsChar s c = containsAny s (· == c)`.

For example:
* `containsAny "hello" (· == 'e') = true`
* `containsAny "abc123" Char.isDigit = true`
* `containsAny "" isUpperChar = false` -/
def containsAny (s : String) (p : Char → Bool) : Bool :=
  s.data.any p

/-- Check whether `s` contains any character from `chars`.
Equivalent to `containsAny s (fun c => c ∈ chars)`.

For example:
* `containsAnyIn "hello" ['x', 'e', 'y'] = true`
* `containsAnyIn "hello" ['x', 'y', 'z'] = false`
* `containsAnyIn "" ['a'] = false` -/
def containsAnyIn (s : String) (chars : List Char) : Bool :=
  s.data.any (fun c => c ∈ chars)

/-- `containsAnyIn s chars` is true iff there exists a character `c ∈ chars` such that
`s.contains c`. This bridges the `List Char` API with the built-in `String.contains`. -/
lemma containsAnyIn_eq_true_iff (s : String) (chars : List Char) :
    containsAnyIn s chars = true ↔ ∃ c ∈ chars, s.contains c = true := by
  simp [containsAnyIn, String.contains_iff, List.any_eq_true, and_comm]

/-- `containsChar` is equivalent to membership in the character data list. -/
lemma containsChar_iff_mem_data (s : String) (c : Char) :
    containsChar s c ↔ c ∈ s.data := by
  simp [containsChar]

/-- The negation of `String.contains` is equivalent to the character not being in the
string's underlying character data. This is the `¬` version of `String.contains_iff`,
giving convenient access to the negative equivalence without needing to apply `not_iff_not`
to `String.contains_iff`. -/
lemma not_contains_iff_not_mem (s : String) (c : Char) : (¬ s.contains c) ↔ c ∉ s.data := by
  simpa using (String.contains_iff (s := s) (c := c)).not

/-- If a character `c` belongs to the underlying character data of a string `s`,
then `s.contains c = true`. This is the forward direction of `String.contains_iff`
and is a convenient lemma for deducing containment from membership proofs.
For example, if `'a' ∈ "abc".data`, then `"abc".contains 'a' = true`. -/
lemma contains_eq_true_of_mem_data (s : String) (c : Char) (h : c ∈ s.data) : s.contains c = true :=
  (String.contains_iff s c).mpr h

/-- Check whether `s` contains every character in `chars`. -/
def containsAllChars (s : String) (chars : List Char) : Bool :=
  chars.all fun c => s.contains c

/-- Check whether `s` contains at least one lowercase ASCII letter (a-z). -/
def hasLower (s : String) : Bool :=
  s.data.any isLowerChar

/-- Check whether `s` contains at least one uppercase ASCII letter (A-Z). -/
def hasUpper (s : String) : Bool :=
  s.data.any isUpperChar

/-- Check whether `s` contains at least one decimal digit (0-9). -/
def hasDigit (s : String) : Bool :=
  s.data.any isDecDigit

/-- Check whether a list of characters contains at least one (Unicode) digit.
This is the `List Char` counterpart of `hasDigit` (which works on `String`
and uses the ASCII-only digit check `isDecDigit`). This version uses the
built-in `Char.isDigit`, which is Unicode-aware.
For example, `hasDigitOnList ['a','1','b'] = true`. -/
def hasDigitOnList (l : List Char) : Bool :=
  l.any Char.isDigit

/-! ## Bitmask operations -/

/-- Compute the bitmask of a single character relative to an `offset`.
`charBit offset c` returns `1 <<< (c.toNat - offset.toNat)`, i.e. a single bit
set at the position of `c` in the alphabet starting from `offset`.
For example, `charBit 'a' 'c' = 4` (bit 2 set), `charBit '0' '5' = 32` (bit 5 set).

This is useful for building bitmask representations of character sets. -/
def charBit (offset : Char) (c : Char) : Nat :=
  1 <<< (c.toNat - offset.toNat)

/-- Convert a string into a bitmask by shifting each character relative to `offset`.
Each character `c` contributes bit `(c.toNat - offset.toNat)` to the mask via `charBit`.
For example, `maskFromString 'a' "ab" = 3` (bits 0 and 1 set). -/
def maskFromString (offset : Char) (s : String) : Nat :=
  s.data.foldl (fun acc c => acc ||| charBit offset c) 0


end String


namespace String

/-! ## Case transformations -/

/-- Return the first character of a string, uppercased, as a singleton string.
Returns `""` for the empty string. -/
def upperFirst (s : String) : String :=
  match s.data with
  | [] => ""
  | c :: _ => (String.mk [c]).toUpper

/-- Return all but the first character of a string, lowercased.
Returns `""` for empty or single-character strings. -/
def lowerRest (s : String) : String :=
  (s.drop 1).toLower

end String


namespace String


/-- Capitalize the first character of a string, leaving the rest unchanged.
Returns the empty string if the input is empty.

Unlike `String.capitalize` (which also lowercases subsequent characters), this
only uppercases the first character via `Char.toUpper`.

For example:
* `capitalizeFirst "hello" = "Hello"`
* `capitalizeFirst "HELLO" = "HELLO"` (rest preserved, unlike `capitalize`)
* `capitalizeFirst "" = ""` -/
def capitalizeFirst (s : String) : String :=
  match s.data with
  | [] => ""
  | ch :: cs => String.mk (Char.toUpper ch :: cs)


lemma capitalizeFirst_empty : capitalizeFirst "" = "" := rfl

lemma length_capitalizeFirst (s : String) :
    (capitalizeFirst s).length = s.length := by
  unfold capitalizeFirst
  cases hs : s.data
  · have : s = "" := String.ext hs
    simp [this]
  · rename_i c cs
    rw [String.length_mk, ← String.length_data s, hs]
    simp

lemma capitalizeFirst_ne_empty_of_ne_empty {s : String} (h : s ≠ "") :
    capitalizeFirst s ≠ "" := by
  intro heq
  have hlen := congrArg String.length heq
  rw [length_capitalizeFirst, String.length_empty] at hlen
  have hpos : s.length > 0 := length_pos_of_ne_empty s h
  omega

/-- Auxiliary recursive function for `capitalizeWords`. Iterate through a list of
characters, capitalizing each alphabetic character that follows a space (or is at
the beginning when `prevSpace = true`). The `prevSpace` flag tracks whether the
previous character was a space.

This is a character-level stateful traversal: spaces are preserved in the output,
and only alphabetic characters (`Char.isAlpha`) are uppercased via `Char.toUpper`.
Non-alphabetic characters after a space (digits, punctuation, etc.) are kept as-is.

For example:
* `capitalizeWordsAux ['h','e','l','l','o',' ','w','o','r','l','d'] true`
  yields `['H','e','l','l','o',' ','W','o','r','l','d']`
* `capitalizeWordsAux [' ',' ','a'] true` yields `[' ',' ','A']` -/
def capitalizeWordsAux (cs : List Char) (prevSpace : Bool) : List Char :=
  match cs with
  | [] => []
  | c :: cs' =>
    let isSpace : Bool := c = ' '
    let newChar : Char :=
      if prevSpace && Char.isAlpha c then Char.toUpper c else c
    newChar :: capitalizeWordsAux cs' isSpace

/-- Capitalize the first letter of each word in a string, where words are separated
by spaces. The first word is also capitalized (as if preceded by a space).
Alphabetic characters immediately following a space are converted to uppercase;
all other characters are left unchanged (including interior letters of words).

Unlike `titleCase` which uses `String.capitalize` (making the first character
uppercase and the rest lowercase), `capitalizeWords` only changes the case of
the first letter of each word, preserving the case of all other characters.

For example:
* `capitalizeWords "hello world" = "Hello World"`
* `capitalizeWords "HELLO WORLD" = "HELLO WORLD"` (already uppercase)
* `capitalizeWords "  leading" = "  Leading"` (leading spaces preserved)
* `capitalizeWords "" = ""` -/
def capitalizeWords (s : String) : String :=
  String.mk (capitalizeWordsAux s.data true)

/-! ## CamelCase conversion -/

/-- Join a list of strings in camelCase style: keep the first string as-is,
capitalize the first character of all subsequent strings, and concatenate them all.
For example, `joinCamelTail ["hello", "world", "foo"] = "helloWorldFoo"`. -/
def joinCamelTail (l : List String) : String :=
  l.headD "" ++ String.join (l.tail.map String.capitalize)

/-- Convert a snake_case string to camelCase by splitting on underscores,
keeping the first segment as-is, and capitalizing subsequent segments.
For example, `snakeToCamel "hello_world_foo" = "helloWorldFoo"`.
Works for any string; characters that aren't lowercase letters are preserved as-is. -/
def snakeToCamel (s : String) : String :=
  joinCamelTail (s.split (fun c => c = '_'))

/-- Convert a list of words into lowerCamelCase: the first word is lowercased,
subsequent words are capitalized (first character uppercase, rest lowercase),
and all are joined without separators. Differs from `joinCamelTail` which
preserves the first word's original case.

For example:
* `joinCamelCase ["hello", "world", "foo"] = "helloWorldFoo"`
* `joinCamelCase ["Hello", "World"] = "helloWorld"`
* `joinCamelCase [] = ""` -/
def joinCamelCase : List String → String
  | [] => ""
  | w0 :: ws' =>
      let first := w0.toLower
      let rest := ws'.map (fun w => String.capitalize w)
      first ++ String.join rest


lemma joinCamelCase_nil : joinCamelCase [] = "" := rfl

lemma joinCamelCase_cons (w : String) (ws : List String) :
    joinCamelCase (w :: ws) =
    w.toLower ++ String.join (ws.map String.capitalize) :=
  rfl

/-- Auxiliary recursive snake_case to camelCase conversion on character lists.
Preserves the case of all characters; only the character immediately following
an underscore `'_'` is uppercased (via `Char.toUpper`). All other characters
(including those following non-underscore characters) are kept as-is.
The `cap` flag indicates whether the next character should be capitalized.

This is a lower-level, case-preserving variant of `snakeToCamel` that operates
on `List Char` rather than `String`. For example:
* `snakeToCamelAux ['h','e','l','l','o','_','w','o','r','l','d'] false = ['h','e','l','l','o','W','o','r','l','d']`
* `snakeToCamelAux ['H','E','L','L','O','_','W','O','R','L','D'] false = ['H','E','L','L','O','W','O','R','L','D']` -/
def snakeToCamelAux (l : List Char) (cap : Bool) : List Char :=
  match l with
  | [] => []
  | '_' :: rest => snakeToCamelAux rest true
  | c :: rest =>
    let c' := if cap then Char.toUpper c else c
    c' :: snakeToCamelAux rest false

/-- A single fold step for iterative snake_case to camelCase conversion on `List Char`.
Given the current state `(acc, cap)` where `acc` is the accumulated output character list
and `cap` indicates whether the next character should be capitalized, process character `c`.

This is designed to be used with `List.foldl`, enabling an iterative (non-recursive)
implementation of snake_case → camelCase conversion. The fold is started with initial
state `([], false)` and the final accumulator (`.fst`) is the result.

For example:
* `List.foldl snakeToCamelStep ([], false) ['h','e','l','l','o','_','w','o','r','l','d']`
  yields `(['h','e','l','l','o','W','o','r','l','d'], false)` — the `.fst` is the camelCase result. -/
def snakeToCamelStep (st : List Char × Bool) (c : Char) : List Char × Bool :=
  match st with
  | (acc, cap) =>
    if c = '_' then (acc, true)
    else if cap then (acc ++ [Char.toUpper c], false)
    else (acc ++ [c], false)

/-! ## TitleCase conversion -/

/-- Convert a string to title case: split on spaces, capitalize each word,
and rejoin with spaces.

For example:
* `titleCase "hello world" = "Hello World"`
* `titleCase "  HELLO   world  " = "  Hello   World  "`
* `titleCase "" = ""`

Note: `String.capitalize` makes the first character uppercase and the rest
lowercase. Multiple consecutive spaces are preserved as-is. -/
def titleCase (s : String) : String :=
  let words := s.split (fun c => c = ' ')
  String.intercalate " " (words.map String.capitalize)


end String
