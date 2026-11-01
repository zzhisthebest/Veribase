import general.String.CharacterStatistics
import general.String.NumericConversion
import general.List.Palindromes
import Mathlib

namespace String

/-- Split a string by a predicate, discarding empty segments. -/
def splitByPredNonEmpty (p : Char → Bool) (s : String) : List String :=
  (s.split p).filter (fun t => t != "")

/-- Split a string into tokens separated by spaces, discarding empty tokens. -/
def splitTokens (s : String) : List String :=
  splitByPredNonEmpty (fun c => c == ' ') s

/-- Check whether substring `sub` occurs at position `i` in `s`. -/
@[reducible]
def isSubstringAt (s sub : String) (i : Nat) : Prop :=
  i + sub.length ≤ s.length ∧ (s.drop i).take sub.length = sub

/-- Extract a substring of length `len` starting at position `start`. -/
def slice (s : String) (start len : Nat) : String :=
  String.mk <| (s.data.drop start).take len

/-! ## Filtering -/

/-- Filter a string, keeping only characters satisfying the predicate. -/
def filter (s : String) (p : Char → Bool) : String :=
  String.mk (s.data.filter p)

/-- Projection: the underlying character list of a filtered string.
`(s.filter p).data = s.data.filter p`. This is the defining property of `String.filter`. -/

lemma filter_data (s : String) (p : Char → Bool) : (s.filter p).data = s.data.filter p := rfl

/-- If a character `c` is in `(s.filter p).data`, then `c` satisfies `p`. -/
lemma mem_filter {p : Char → Bool} {s : String} {c : Char} (h : c ∈ (s.filter p).data) : p c := by
  rw [filter_data] at h
  rcases List.mem_filter.mp h with ⟨_, hp⟩
  exact hp

/-- Filtering a string by a predicate never increases its length:
`(s.filter p).length ≤ s.length`. This holds for any predicate `p`,
including specializations like `Char.isAlpha` (alpha-only) and `Char.isDigit`
(digit-only) filters. -/
lemma length_filter_le (s : String) (p : Char → Bool) : (s.filter p).length ≤ s.length := by
  unfold filter
  simpa using List.length_filter_le p s.data

/-- Filter characters by predicate `p` and simultaneously apply transformation `f`
to the kept characters. Equivalent to `(s.filter p).map f` but done in a single pass.
For example, `filterMap Char.isAlpha Char.toUpper "a1b2c3" = "ABC"`. -/
def filterMap (p : Char → Bool) (f : Char → Char) (s : String) : String :=
  String.mk (s.data.filterMap (λ c => if p c then some (f c) else none))

/-- `filterMap p f s` is equivalent to mapping `f` over characters of `s` that satisfy `p`.
This lemma relates `filterMap` to the composition `String.mk ∘ (List.map f) ∘ (List.filter p)`. -/
lemma filterMap_eq (p : Char → Bool) (f : Char → Char) (s : String) :
    filterMap p f s = String.mk ((s.data.filter p).map f) := by
  unfold filterMap
  apply congrArg String.mk
  induction s.data with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : p c
    · simp [h, ih]
    · simp [h, ih]

/-! ## Normalization utilities -/

/-- Apply a function to a string after trimming leading and trailing whitespace.
This is a general combinator that captures the pattern `f (s.trim)`.
For example, `mapTrim String.capitalize "  hello world  " = "Hello world"`.

Note that `normalize s = mapTrim String.toLower s`. -/
def mapTrim (f : String → α) (s : String) : α := f (String.trim s)

/-- Trim a string; return `none` if the result is empty, `some trimmed` otherwise. -/
def trimToOpt (s : String) : Option String :=
  let t := s.trim
  if t = "" then none else some t

/-- Normalize a string by trimming surrounding whitespace and converting all characters
to lowercase. Useful for case-insensitive comparison after stripping padding. -/
def normalize (s : String) : String :=
  s.trim.toLower

/-- Collapse all whitespace in a string: trim leading and trailing whitespace,
then replace any consecutive whitespace with a single space. This is a common
preprocessing step for text normalization.

For example:
* `collapseWhitespace "  hello   world  " = "hello world"`
* `collapseWhitespace "a\tb\nc" = "a b c"` (tabs and newlines become spaces) -/
def collapseWhitespace (s : String) : String :=
  let trimmed := s.trim
  let parts := (trimmed.splitOn " ").filter (fun s => s ≠ "")
  String.intercalate " " parts

/-- `collapseWhitespace` expands to `intercalate " "` of the non-empty split of `s.trim`. -/
lemma collapseWhitespace_eq (s : String) :
    collapseWhitespace s = String.intercalate " " ((s.trim.splitOn " ").filter (fun s => s ≠ "")) :=
  rfl

/-- Normalize a string to alphabetic words: trim, convert to lowercase, keep only
alphabetic characters and spaces (`Char.isAlphaOrSpace`), then collapse consecutive
spaces into single spaces. Non-alphabetic characters (digits, punctuation, etc.)
are discarded.

For example:
* `normalizeAlphaWords "  Hello, World! 123  " = "hello world"`
* `normalizeAlphaWords "ABC  DEF  GHI" = "abc def ghi"`
* `normalizeAlphaWords "" = ""` -/
def normalizeAlphaWords (s : String) : String :=
  let trimmed := s.trim
  let lowered := trimmed.toLower
  let chars := lowered.toList
  let filtered := chars.filter Char.isAlphaOrSpace
  let rebuilt := String.mk filtered
  let parts := rebuilt.splitOn " "
  let nonempty := parts.filter (fun t => t ≠ "")
  String.intercalate " " nonempty

/-- Case-insensitive equality predicate on strings.
Compares two strings by first converting both to lowercase via `String.toLower`,
then checking equality. For example, `caseInsensitiveEq "Hello" "heLLo" = true`. -/
def caseInsensitiveEq (a b : String) : Bool :=
  String.toLower a = String.toLower b

/-- Check whether there exists a string in `words` that equals `w` case-insensitively.
Compares by converting both to lowercase. This generalizes `caseInsensitiveEq` to list
membership: it returns `true` iff `w` (case-insensitively) appears in `words`.
For example, `anyCaseInsensitive ["Hello", "World"] "hello" = true`. -/
def anyCaseInsensitive (words : List String) (w : String) : Bool :=
  words.any (fun sw => sw.toLower = w.toLower)

/-- Case-insensitive less-than-or-equal relation on strings (as a `Prop`).
`ciLe a b` holds iff the lowercase version of `a` is ≤ the lowercase version of `b`.
For example, `ciLe "Apple" "banana"` holds because `"apple" ≤ "banana"`.

This is the `Prop` counterpart of comparing via `String.toLower` with `≤`.
For the `Bool` version, use the comparison `String.toLower a ≤ String.toLower b`
directly (which is decidable). -/
def ciLe (a b : String) : Prop :=
  String.toLower a ≤ String.toLower b

/-- `ciLe` is decidable: `String.toLower a ≤ String.toLower b` is a decidable proposition
for any strings `a` and `b`. This instance enables `List.insertionSort ciLe` and similar
decidable-relation APIs for case-insensitive string sorting. -/
instance decidableRelCiLe : DecidableRel ciLe :=
  inferInstanceAs (DecidableRel (fun a b : String => String.toLower a ≤ String.toLower b))

/-- `ciLe` is total on `String`: for any two strings `a` and `b`,
either `ciLe a b` or `ciLe b a` holds. This is needed to use `ciLe` with
`List.insertionSort` (which requires `IsTotal`). -/
instance totalCiLe : IsTotal String ciLe where
  total a b := le_total (String.toLower a) (String.toLower b)

/-- `ciLe` is transitive on `String`: if `ciLe a b` and `ciLe b c`, then `ciLe a c`.
This follows from transitivity of `≤` on `String`, since `ciLe` compares lowercase forms.
This instance is needed together with `totalCiLe` to use `ciLe` with
`List.insertionSort` (which requires both `IsTotal` and `IsTrans`). -/
instance transCiLe : IsTrans String ciLe :=
  ⟨fun a b c h₁ h₂ => le_trans h₁ h₂⟩

/-- Case-insensitive `≤` comparison on strings as a `Bool`.
`ciLeBool a b` is `true` iff the lowercase version of `a` is ≤ the lowercase version of `b`.
This is the `Bool` counterpart of `ciLe`, suitable for `List.mergeSort` and other
`Bool`-comparator APIs.

For example, `ciLeBool "Apple" "banana" = true` because `"apple" ≤ "banana"`. -/
def ciLeBool (a b : String) : Bool :=
  decide (String.toLower a ≤ String.toLower b)

/-- `ciLeBool a b = true` iff `ciLe a b`. This bridges the `Bool` and `Prop` versions. -/

lemma ciLeBool_eq_true_iff (a b : String) : ciLeBool a b = true ↔ ciLe a b := by
  simp [ciLeBool, ciLe]

/-- `ciLeBool` is transitive: if `ciLeBool a b` and `ciLeBool b c`, then `ciLeBool a c`. -/
lemma ciLeBool_trans {a b c : String} (h₁ : ciLeBool a b = true) (h₂ : ciLeBool b c = true) :
    ciLeBool a c = true := by
  unfold ciLeBool at h₁ h₂ ⊢
  have h₁' : String.toLower a ≤ String.toLower b := of_decide_eq_true h₁
  have h₂' : String.toLower b ≤ String.toLower c := of_decide_eq_true h₂
  exact decide_eq_true (le_trans h₁' h₂')

/-- `ciLeBool` is total: for any `a, b`, either `ciLeBool a b` or `ciLeBool b a` holds. -/
lemma ciLeBool_total (a b : String) : (ciLeBool a b || ciLeBool b a) = true := by
  unfold ciLeBool
  rcases le_total (String.toLower a) (String.toLower b) with (h | h)
  · have hd : decide (String.toLower a ≤ String.toLower b) = true := decide_eq_true h
    rw [hd]; simp
  · have hd : decide (String.toLower b ≤ String.toLower a) = true := decide_eq_true h
    rw [hd]; simp

/-- Filter a string, keeping only characters satisfying `keep`, and transform each
remaining character with `transform`. Returns a `List Char` for convenient further
list processing (e.g., palindrome checking). This generalizes `filterAlphaToLower`:
`filterAlphaToLower s = normalizeChars Char.isAlpha Char.toLower s`. -/
def normalizeChars (keep : Char → Bool) (transform : Char → Char) (s : String) : List Char :=
  (s.data.filter keep).map transform

/-- Filter a string to keep only alphabetic characters, then convert them all to lowercase.
Returns a `List Char` for convenient further list processing (e.g., palindrome checking).
Non-alphabetic characters are silently dropped.
For example: `filterAlphaToLower "A man, a plan: Panama"` yields
`['a','m','a','n','a','p','l','a','n','p','a','n','a','m','a']`. -/
def filterAlphaToLower (s : String) : List Char :=
  normalizeChars Char.isAlpha Char.toLower s

/-- Filter a string to keep only alphanumeric characters (letters and digits), then convert
them all to lowercase. Returns a `List Char` for convenient further list processing
(e.g., palindrome checking). Non-alphanumeric characters (punctuation, spaces, etc.)
are silently dropped.

This is a common preprocessing step in palindrome problems:
`filterAlphaNumToLower "A man, a plan, a canal: Panama!"` yields
`['a','m','a','n','a','p','l','a','n','a','c','a','n','a','l','p','a','n','a','m','a']`. -/
def filterAlphaNumToLower (s : String) : List Char :=
  normalizeChars Char.isAlphaNum Char.toLower s

/-- Clean a string by keeping only alphanumeric characters (letters and digits)
and converting them to lowercase. Returns a `String`.
This is the `String`-valued version of `filterAlphaNumToLower`;
for example, `cleanAlphaNum "A man, a plan: Panama!" = "amanaplanpanama"`. -/
def cleanAlphaNum (s : String) : String :=
  String.mk (filterAlphaNumToLower s)

/-- Clean a string for text processing: convert to lowercase, keep only alphanumeric
characters, spaces, and apostrophes (via `Char.isAlphaNumOrSpaceOrApostrophe`),
collapse consecutive whitespace into single spaces, and trim surrounding whitespace.

This is a common preprocessing step for text matching, search, and comparison tasks
where punctuation is stripped but spaces and contractions (apostrophes) are preserved.

For example:
* `cleanText "Hello, World!" = "hello world"`
* `cleanText "Don't panic!" = "don't panic"`
* `cleanText "   Extra   Spaces   " = "extra spaces"` -/
def cleanText (s : String) : String :=
  let lowered := s.toLower
  let filtered := lowered.filter Char.isAlphaNumOrSpaceOrApostrophe
  collapseWhitespace filtered

/-! ### Cleaned palindrome -/

/-- Check whether a string is a palindrome after cleaning: keep only alphanumeric
characters, convert to lowercase, then check whether the resulting character list
equals its reverse. This is the standard definition used in palindrome problems
that ignore case, punctuation, and whitespace (e.g., "A man, a plan, a canal: Panama!").

Equivalent to `List.isPalindrome (filterAlphaNumToLower s)`. -/
def isAlphaNumPalindrome (s : String) : Bool :=
  List.isPalindrome (filterAlphaNumToLower s)


lemma isAlphaNumPalindrome_nil : isAlphaNumPalindrome "" := by
  first
  | (solve
    | rfl
    | simp_all [isAlphaNumPalindrome]
    | omega
    | aesop
    | simp_all [isAlphaNumPalindrome, List.foldl, List.foldr]
    | simp_all [isAlphaNumPalindrome, Nat.absDiff])

/-- `isAlphaNumPalindrome s` is true iff the cleaned character list
(alphanumeric, lowercased) equals its reverse. -/
lemma isAlphaNumPalindrome_eq_true_iff (s : String) :
    isAlphaNumPalindrome s = true ↔ (filterAlphaNumToLower s = (filterAlphaNumToLower s).reverse) := by
  simp [isAlphaNumPalindrome, List.isPalindrome]

/-- Filter a string by a predicate, then take at most `n` characters.
Equivalent to `String.filter s p |>.take n`, but more efficient since
it avoids constructing the intermediate full filtered string. -/
def filterTake (s : String) (p : Char → Bool) (n : Nat) : String :=
  String.mk ((s.data.filter p).take n)

lemma filterTake_length_le (s : String) (p : Char → Bool) (n : Nat) :
    (filterTake s p n).length ≤ n := by
  unfold filterTake
  simp [String.length_mk, List.length_take]

/-- Remove all occurrences of character `c` from string `s`. -/
def stripChar (c : Char) (s : String) : String :=
  String.mk (s.data.filter (· ≠ c))

lemma stripChar_not_contains (s : String) (c : Char) : ¬ (stripChar c s).contains c := by
  rw [String.contains_iff]
  unfold stripChar
  simp [List.mem_filter]

/-- Returns the prefix of `s` consisting of characters that differ from `c`.
Equivalent to `s.takeWhile (fun x => x ≠ c)`, i.e., the prefix before the first occurrence of `c`.
For example, `takeWhileDiff "abc;def" ';' = "abc"`. -/
def takeWhileDiff (s : String) (c : Char) : String :=
  s.takeWhile (fun x => x ≠ c)

/-- In any string, the length of the `takeWhile` prefix (by predicate `p`) is bounded by
the total length. This is the string-level counterpart of `List.length_takeWhile_le`. -/
lemma length_takeWhile_le (s : String) (p : Char → Bool) :
    (s.takeWhile p).length ≤ s.length := by
  rw [String.takeWhile_eq]
  exact List.length_takeWhile_le s.data p

end String

namespace String

/-! ## String truncation -/

/-- Truncate a string by keeping the first `prefixLen` characters and the last `suffixLen`
characters, with a `separator` between them. If `s.length ≤ maxLen`, the string is returned
unchanged. This is typically used to abbreviate long strings like `"VeryLongFileName..."` by
showing the beginning and end with an ellipsis (`...`) in between.

For example:
* `truncateWith 10 4 3 "..." "HelloWorld" = "Hell...rld"`
* `truncateWith 50 25 20 "..." "Short" = "Short"` (no truncation needed) -/
def truncateWith (maxLen prefixLen suffixLen : Nat) (separator : String) (s : String) : String :=
  if s.length ≤ maxLen then
    s
  else
    (s.take prefixLen) ++ separator ++ (s.drop (s.length - suffixLen))

/-- When the string length exceeds `maxLen`, `truncateWith` produces the prefix-separator-suffix
form rather than returning the string unchanged. -/
lemma truncateWith_of_not_le {maxLen prefixLen suffixLen : Nat} {separator s : String} (h : ¬ s.length ≤ maxLen) :
    truncateWith maxLen prefixLen suffixLen separator s =
      (s.take prefixLen) ++ separator ++ (s.drop (s.length - suffixLen)) := by
  unfold truncateWith
  simp [h]

/-- Truncate a string to fit within `limit` characters, appending `suffix` when truncation
is needed. Returns a pair `(truncated, removed)` where `removed` is the number of characters
that were cut off. If `s.length ≤ limit`, returns `(s, 0)` unchanged.

`suffixLen` should equal `suffix.length`; it is accepted as a separate argument so callers
that already know the suffix length can avoid recomputation.

For example:
* `truncateAppending "Hello World" 10 "..." 3 = ("Hello W...", 2)`
* `truncateAppending "Short" 10 "..." 3 = ("Short", 0)` -/
def truncateAppending (s : String) (limit : Nat) (suffix : String) (suffixLen : Nat) : String × Nat :=
  if h : s.length ≤ limit then
    (s, 0)
  else
    (s.take (limit - suffixLen) ++ suffix, s.length - (limit - suffixLen))

/-- Specification lemma for `truncateAppending`: the result is the original string when it fits,
and the truncated form with the suffix appended when it doesn't. -/
lemma truncateAppending_spec (s : String) (limit : Nat) (suffix : String) (suffixLen : Nat) :
    ((s.length ≤ limit) → ((truncateAppending s limit suffix suffixLen).fst = s ∧ (truncateAppending s limit suffix suffixLen).snd = 0)) ∧
    ((limit < s.length) → ((truncateAppending s limit suffix suffixLen).fst = s.take (limit - suffixLen) ++ suffix ∧ (truncateAppending s limit suffix suffixLen).snd = s.length - (limit - suffixLen))) := by
  unfold truncateAppending
  split
  · rename_i h
    constructor
    · intro _
      simp
    · intro hlt
      have : limit < limit := Nat.lt_of_lt_of_le hlt h
      exact absurd this (Nat.lt_irrefl limit)
  · rename_i h
    constructor
    · intro hle
      exact absurd hle h
    · intro _
      simp

end String

namespace String

/-! ## Validated conditional mapping -/

/-- Apply a character transformation `f` to `s` if all characters satisfy predicate `p`;
otherwise return `err`. This is a general combinator for validated string
transformations, reusable across different predicates and mappings.

For example:
* `applyIfAll "abc" Char.isDigit id "error" = "error"` (contains non-digits)
* `applyIfAll "123" (· ≥ '0') (·) "NAN" = "123"` (all digits) -/
def applyIfAll (s : String) (p : Char → Bool) (f : Char → Char) (err : String) : String :=
  if s.data.all p then
    s.map f
  else
    err

/-- Replace every character in `s` satisfying predicate `f` with `replacement`.
The string length is unchanged; only matching characters are substituted.

For example:
* `replaceWhere (· == ' ') '-' "a b c" = "a-b-c"`
* `replaceWhere isVowel '_' "hello" = "h_ll_"` -/
def replaceWhere (f : Char → Bool) (replacement : Char) (s : String) : String :=
  s.map (fun c => if f c then replacement else c)

/-- The character data of `replaceWhere` is the list obtained by mapping each character
`c` to `replacement` if `f c` and to `c` otherwise. This `@[simp]` lemma allows
rewriting `(replaceWhere f r s).data` to `s.data.map (fun c => if f c then r else c)`. -/

theorem replaceWhere_data (f : Char → Bool) (replacement : Char) (s : String) :
    (replaceWhere f replacement s).data = s.data.map (fun c => if f c then replacement else c) := by
  simp [replaceWhere, String.map_eq]

end String

namespace String

/-! ### Substring replacement with multiple pairs -/

/-- Apply a sequence of `(old, new)` string replacements sequentially, from first to last.
Each replacement replaces all occurrences of `old` with `new` in the current string.
For example: `"abc".replaceAll [("a", "x"), ("b", "y")] = "xyc"`. -/
def replaceAll (s : String) (replacements : List (String × String)) : String :=
  replacements.foldl (fun s' (old, new) => s'.replace old new) s

/-- `String.replaceAll` with an empty replacement list leaves the string unchanged. -/

lemma replaceAll_nil (s : String) : s.replaceAll [] = s := rfl

end String


namespace String

/-! ## Reverse -/

/-- Reverse a string by reversing its underlying list of characters. -/
def reverse (s : String) : String :=
  String.mk s.data.reverse

/-- Reverse the order of segments in `s` that are separated by `sep`.
Splits `s` at each occurrence of `sep`, reverses the resulting list of segments,
and rejoins them with `sep`.

For example:
* `reverseSeparated '.' "file.name.txt" = "txt.name.file"`
* `reverseSeparated ' ' "hello world" = "world hello"`
* `reverseSeparated ' ' "a b c" = "c b a"` -/
def reverseSeparated (sep : Char) (s : String) : String :=
  String.intercalate (String.singleton sep) ((s.split (fun c => c = sep)).reverse)

/-! ## Palindrome -/

/-- Check whether a string is a palindrome (its character list is a palindrome list). -/
def isPalindrome (s : String) : Bool :=
  List.isPalindrome s.data


lemma isPalindrome_nil : isPalindrome "" := by
  first
  | (solve
    | rfl
    | simp_all [isPalindrome]
    | omega
    | aesop
    | simp_all [isPalindrome, List.foldl, List.foldr]
    | simp_all [isPalindrome, Nat.absDiff])

/-- Check whether a string reads the same forwards and backwards using `decide` and `reverse`.
This is an alternative to `isPalindrome` (which uses `List.isPalindrome`), working directly
with string equality and `reverse`. The `decide` formulation makes it decidable and convenient
for rewriting. -/
def isPalindromeStr (s : String) : Bool :=
  decide (s = reverse s)

/-- `String.isPalindromeStr s` is `true` iff `s` equals its own reverse. -/
lemma isPalindromeStr_eq_true_iff (s : String) :
    isPalindromeStr s = true ↔ s = reverse s := by
  unfold isPalindromeStr
  simp

/-- Return `s` if it is already a palindrome, otherwise `s ++ s.reverse`.
This is the standard "force to palindrome by appending reverse" operation. -/
def toPalindrome (s : String) : String :=
  if isPalindrome s then s else s ++ reverse s

/-- For any string `s`, `s ++ s.reverse` is a palindrome:
its character data equals its own reverse. -/
theorem reverse_append_self_palindrome (s : String) :
    (s ++ reverse s).data = (s ++ reverse s).data.reverse := by
  simp [reverse, String.data_append, List.reverse_append]

end String

namespace String

/-! ## Circular shifts -/

/-- Left circular shift of a string by `k` positions.
Drops the first `k % str.length` characters and appends them at the end.
If the string is empty, returns it unchanged. -/
def circLeftShift (str : String) (k : Nat) : String :=
  let n := str.length
  if _ : n = 0 then str else
    let l := k % n
    (str.drop l) ++ (str.take l)

/-- Right circular shift of a string by `k` positions.
Equivalent to dropping the last `k % str.length` characters and prepending them.
If the string is empty, returns it unchanged. -/
def circRightShift (str : String) (k : Nat) : String :=
  let n := str.length
  if _ : n = 0 then str else
    let l := n - k % n
    (str.drop l) ++ (str.take l)

end String


namespace String


/-- Rotate a string to the right by `k` positions: take the last `k` characters
and move them to the front. When `k ≤ s.length`, this is a standard right rotation.
When `k > s.length`, natural subtraction truncates at zero, so `rotateRight s k = s`.
For a variant that wraps around via `k % s.length`, see `circRightShift`.

For example:
* `rotateRight "abcde" 2 = "deabc"`
* `rotateRight "abcde" 0 = "abcde"`
* `rotateRight "" 5 = ""` -/
def rotateRight (s : String) (k : Nat) : String :=
  let len := s.length
  (s.drop (len - k)) ++ (s.take (len - k))

/-- Compute the rotation of `s` at index `i`: drop the first `i` characters
and append them at the end. This is a left rotation: `rotationAt "abc" 1 = "bca"`.
Unlike `circLeftShift`, this does not wrap via modulo — if `i ≥ s.length`, the
result is `s.drop i ++ s.take i` (with `s.take i = s` and `s.drop i = ""`). -/
def rotationAt (s : String) (i : Nat) : String :=
  s.drop i ++ s.take i

/-- Check whether `s2` is a rotation of `s1`. Two strings are rotations of each other if
they have the same length and there exists some shift `k` such that `s2 = rotationAt s1 k`.
For example, `isRotation "abcde" "cdeab" = true` and `isRotation "abcde" "abcdx" = false`. -/
def isRotation (s1 s2 : String) : Bool :=
  if s1.length = s2.length then
    List.any (List.range s1.length) (λ k => s2 = rotationAt s1 k)
  else
    false

/-- The length of a rotation `s.drop n ++ s.take n` equals the original string length.
This is the string-level counterpart of `List.length_drop_append_take`. -/
lemma length_rotationAt (s : String) (n : Nat) : (rotationAt s n).length = s.length := by
  dsimp [rotationAt]
  rw [← String.length_data ((s.drop n) ++ (s.take n)), String.data_append,
    String.data_drop, String.data_take, ← String.length_data s]
  exact List.length_drop_append_take s.data n

/-- If a character is in the data of a rotation `(s.drop n) ++ (s.take n)`,
it was in the original string. This is the membership counterpart of
`length_rotationAt`. -/
lemma mem_data_of_mem_rotationAt_data (s : String) (n : Nat) {c : Char}
    (h : c ∈ (rotationAt s n).data) : c ∈ s.data := by
  dsimp [rotationAt] at h
  rw [String.data_drop, String.data_take] at h
  exact List.mem_of_mem_append_drop_take h

/-! ## Rotation with Int offset -/

/-- Rotate a string by `n` positions. Positive `n` rotates right (moves characters
from the end to the front), negative `n` rotates left.
Uses `Int.nonnegMod` to normalize the offset into `[0, s.length)`.
Returns the string unchanged if it is empty. -/
def rotate (s : String) (n : Int) : String :=
  let len := s.length
  if len = 0 then s else
    let k_int : Int := Int.nonnegMod n (len : Int)
    let k : Nat := k_int.toNat
    s.drop (len - k) ++ s.take (len - k)

/-- Find the index of the lexicographically smallest rotation of `s` among indices
`0..n-1`. Structurally recursive on `n`. Uses `rotationAt` to compute each rotation
and compares them lexicographically via `String`'s `<`. -/
def findMinRotationIdx (s : String) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let prev := findMinRotationIdx s n
    let rotN := rotationAt s n
    let rotPrev := rotationAt s prev
    if rotN < rotPrev then n else prev

/-- Dropping `s.length` characters gives the empty string. -/

lemma drop_length (s : String) : s.drop s.length = "" := by
  apply String.ext; simp

/-- If `s.length ≤ i`, then `s.drop i = ""`. This generalizes `drop_length` to any index
`i` at or beyond the string's length. -/
lemma drop_eq_empty_of_length_le (s : String) (i : Nat) (h : s.length ≤ i) : s.drop i = "" := by
  rw [String.drop_eq]
  have h' : s.data.length ≤ i := by
    simpa using h
  have hdrop : s.data.drop i = [] := List.drop_eq_nil_of_le h'
  simpa [hdrop]

/-- Taking `s.length` characters gives `s` itself. -/

lemma take_length (s : String) : s.take s.length = s := by
  apply String.ext; simp

/-- Taking characters from the empty string yields the empty string.
This is the counterpart to `take_zero` (which fixes `n = 0` for any `s`)
and `drop_eq_empty_of_length_le` (which fixes `s.drop i` when `i` is past the end). -/

lemma take_empty (n : Nat) : ("".take n : String) = "" := by
  rw [String.take_eq]
  simp

/-- If `s.length ≤ i`, then `(s.drop i).take n = ""`.
Combines `drop_eq_empty_of_length_le` and `take_empty`. -/
lemma drop_take_eq_empty_of_length_le (s : String) (i n : Nat) (h : s.length ≤ i) :
    (s.drop i).take n = "" := by
  rw [drop_eq_empty_of_length_le s i h, take_empty]

/-- Dropping zero characters gives the original string. -/

lemma drop_zero (s : String) : s.drop 0 = s := by
  apply String.ext; simp


lemma rotateRight_zero (s : String) : rotateRight s 0 = s := by
  unfold rotateRight
  simp only [Nat.sub_zero]
  rw [drop_eq_empty_of_length_le s s.length (by omega), take_length]
  simp


lemma rotateRight_length (s : String) : rotateRight s s.length = s := by
  apply String.ext
  simp [rotateRight]

lemma circRightShift_length (s : String) : circRightShift s s.length = s := by
  by_cases h : s.length = 0
  · simp [circRightShift, h]
  · simpa [circRightShift, h, rotateRight] using rotateRight_zero s

lemma rotateRight_eq_circRightShift_of_le (s : String) (k : Nat) (h : k ≤ s.length) :
    rotateRight s k = circRightShift s k := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · simp [rotateRight, circRightShift, Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le k) hlt), Nat.mod_eq_of_lt hlt]
  · rw [rotateRight_length, circRightShift_length]


end String


namespace String


/-- Map a function over segments separated by a given character in a string.
Splits `s` on `sep`, applies `f` to each segment, and joins them back with `sep`. -/
def mapWords (sep : Char) (f : String → String) (s : String) : String :=
  String.intercalate (String.mk [sep]) ((s.split (fun c => c = sep)).map f)

/-- Transform each space-separated word in string `s` using function `f`,
rejoining with spaces. This is `mapWords ' '` with the argument order
optimized for dot notation: `text.transformWords f`.

For example:
* `"hello world".transformWords (fun w => w.reverse) = "olleh dlrow"`
* `"one two".transformWords (fun w => w ++ "!") = "one! two!"` -/
def transformWords (s : String) (f : String → String) : String :=
  mapWords ' ' f s

/-- Map a function over each segment of a delimited string: split on `delim`,
trim each segment, apply `f`, then join the results with `sep`.
This generalizes `mapWords` by allowing different split and join separators,
and by trimming each segment before applying the function.

For example, `mapDelimited id ';' "; " "foo; bar ; baz" = "foo; bar; baz"`. -/
def mapDelimited (f : String → String) (delim : Char) (sep : String) (value : String) : String :=
  String.intercalate sep
    ((value.split (fun c => c = delim)).map (fun g => f (String.trim g)))

/-- Reverse the characters of each word (space-separated segment) in a string.
For example, `reverseWords "hello world" = "olleh dlrow"`.
Equivalent to `mapWords ' ' reverse s`. -/
def reverseWords (s : String) : String :=
  mapWords ' ' reverse s


/-! ## Reverse word order -/

/-- Reverse the order of space-separated words in a string.
For example, `reverseWordOrder "hello world" = "world hello"`.
Unlike `reverseWords` which reverses the characters within each word,
`reverseWordOrder` reverses the order of the words themselves.
Uses `splitTokens` to split on spaces (discarding empty tokens), then
`String.intercalate` to join the reversed list with spaces. -/
def reverseWordOrder (s : String) : String :=
  String.intercalate " " ((splitTokens s).reverse)


lemma reverseWordOrder_empty : reverseWordOrder "" = "" := by
  have hs : "".split (fun c => c == ' ') = [""] := by
    unfold String.split
    rw [String.splitAux.eq_1]
    simp [String.atEnd]
    rfl
  simp [reverseWordOrder, splitTokens, splitByPredNonEmpty, hs, String.intercalate]


end String

namespace String

/-! ## Element removal at index -/

/-- Remove the character at index `i` from string `s` by concatenating
the prefix before `i` with the suffix after `i + 1`.
If `i ≥ s.length`, the result equals `s` (since `take` and `drop` clamp). -/
def removeAt (s : String) (i : Nat) : String :=
  s.take i ++ s.drop (i + 1)

/-- Removing a character at a valid index `i < s.length` reduces the string length by 1. -/
lemma removeAt_length (s : String) (i : Nat) (h : i < s.length) :
    (removeAt s i).length = s.length - 1 := by
  dsimp [removeAt]
  rw [← String.length_data (s.take i ++ s.drop (i + 1)), String.data_append,
    String.data_take, String.data_drop]
  rw [List.length_append, List.length_take, List.length_drop]
  have h_data : i < s.data.length := by
    rwa [← String.length_data] at h
  have hi : i ≤ s.data.length := Nat.le_of_lt h_data
  rw [Nat.min_eq_left hi]
  have hi1 : i + 1 ≤ s.data.length := by omega
  rw [← String.length_data s]
  omega

end String


namespace String

/-! ## Chunking: split a string into fixed-size chunks -/

/-- The length of the `i`-th chunk when splitting `n` items into chunks of size `cs`.
We always take at most `cs` items, and fewer for the last chunk if `n` is not
evenly divisible by `cs`. -/
def chunkLength (n cs i : Nat) : Nat := min cs (n - i * cs)

/-- Extract the `i`-th chunk of size `cs` from string `s`.
For example, `extractChunk "abcdefgh" 3 1 = "def"`. -/
def extractChunk (s : String) (cs i : Nat) : String :=
  (s.drop (i * cs)).take (chunkLength s.length cs i)

/-- The length of `extractChunk s cs i` equals `chunkLength s.length cs i`. -/
lemma extractChunk_length (s : String) (cs i : Nat) :
    (extractChunk s cs i).length = chunkLength s.length cs i := by
  dsimp [extractChunk, chunkLength]
  rw [String.take_eq, String.drop_eq]
  simp only [String.length, List.length_take, List.length_drop]
  omega

/-! ## Overlapping substring occurrences -/

/-- All indices in `s` where substring `sub` occurs, counting overlapping occurrences
(i.e., checking `isSubstringAt` at every position `i` where the substring fits).

Returns a `Finset Nat` of starting positions. Use `.card` to get the count. -/
def overlappingOccurrences (s sub : String) : Finset Nat :=
  (Finset.range s.length).filter (fun i => isSubstringAt s sub i)

/-- Membership in `overlappingOccurrences` is equivalent to `isSubstringAt` with an index
within range of `s.length`. -/
lemma mem_overlappingOccurrences_iff (s sub : String) (i : Nat) :
    i ∈ overlappingOccurrences s sub ↔
    i ∈ Finset.range s.length ∧ isSubstringAt s sub i := by
  unfold overlappingOccurrences
  simp [isSubstringAt]

/-- Overlapping occurrences in an empty text is always empty. -/

lemma overlappingOccurrences_empty_text (sub : String) :
    overlappingOccurrences "" sub = ∅ := by
  unfold overlappingOccurrences
  ext i
  simp [isSubstringAt]

/-- The cardinality of overlapping occurrences in an empty text is zero. -/
lemma overlappingOccurrences_card_zero_of_empty_text (sub : String) :
    (overlappingOccurrences "" sub).card = 0 := by
  simp [overlappingOccurrences_empty_text]

/-- Count overlapping occurrences of `sub` in `s`. Returns 0 for empty `s` or empty `sub`.
This counts every starting position where `isSubstringAt` holds, including overlaps. -/
def countOverlappingSubstrings (s sub : String) : Nat :=
  if sub = "" ∨ s = "" then 0 else
    (overlappingOccurrences s sub).card

/-- When `s` or `sub` is empty, `countOverlappingSubstrings` returns 0. -/

lemma countOverlappingSubstrings_zero_of_empty (s sub : String)
    (h : sub = "" ∨ s = "") : countOverlappingSubstrings s sub = 0 := by
  unfold countOverlappingSubstrings
  simp [h]

/-! ### Substring position search (List-valued)

`substringPositions text pattern` returns all starting positions `i` in `text`
where the substring of exactly `pattern.length` starting at `i` equals `pattern`.
This is the `List`-valued companion to `overlappingOccurrences` (which returns a `Finset`).

For example:
* `substringPositions "hello" "l" = [2, 3]`
* `substringPositions "aaaa" "aa" = [0, 1, 2]` (overlapping)
* `substringPositions "abc" "x" = []` -/

/-- Find all starting positions where `pattern` occurs as a substring of `text`,
counting overlapping occurrences. For each position `i` in the range
`[0, text.length - pattern.length]`, checks whether the substring of length
`pattern.length` at `i` equals `pattern`.

If `pattern` is longer than `text`, the range is empty and the result is `[]`.
If `pattern` is empty, returns all positions from `0` to `text.length`
(vacuously equal). -/
def substringPositions (text : String) (pattern : String) : List Nat :=
  (List.range (text.length - pattern.length + 1)).filter (fun i => (text.drop i).take pattern.length = pattern)

/-! ### Trimming trailing characters -/

/-- Remove trailing characters from the end of `s` that satisfy predicate `p`.
This generalizes trimming of any suffix — whitespace, punctuation, digits, etc.
For example, `trimStringEndWhere Char.isSpace "hello   " = "hello"`. -/
def trimStringEndWhere (p : Char → Bool) (s : String) : String :=
  String.mk (s.data.reverse.dropWhile p |>.reverse)

/-- Remove trailing whitespace characters from the end of a string.
Equivalent to `trimStringEndWhere Char.isSpace`.
For example, `trimStringEnd "hello   \t" = "hello"`. -/
def trimStringEnd (s : String) : String :=
  trimStringEndWhere Char.isSpace s

/-! ## Sublists (subsequences) by length

These functions compute all sublists (i.e., subsequences: ordered selections of
characters, not necessarily contiguous) of a given length from a string.
-/

/-- All sublists (subsequences) of `s` of length `n`, returned as strings.
Each sublist preserves the relative order of characters from the original string,
but characters need not be contiguous. For example,
`sublistsOfLength "abc" 2 = ["ab", "ac", "bc"]`.

This wraps `List.sublistsLen n s.data` and converts each result to a `String` via
`String.mk`. -/
def sublistsOfLength (s : String) (n : ℕ) : List String :=
  (List.sublistsLen n s.data).map String.mk

/-- Characterisation lemma for `mem_sublistsOfLength`: a string `t` is a member
of `sublistsOfLength s n` iff `t.length = n` and `t.data` is a sublist of `s.data`.
This bridges `String`-level reasoning with `List.Sublist`. -/
lemma mem_sublistsOfLength {s t : String} {n : ℕ} :
    t ∈ sublistsOfLength s n ↔ t.length = n ∧ List.Sublist t.data s.data := by
  dsimp [sublistsOfLength]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨l, hl, rfl⟩
    rcases List.mem_sublistsLen.mp hl with ⟨hsub, hlen⟩
    exact ⟨hlen, by simpa⟩
  · intro ⟨hlen, hsub⟩
    have hmem_sublists : t.data ∈ List.sublistsLen n s.data := by
      rw [List.mem_sublistsLen]
      exact ⟨hsub, by simp [hlen]⟩
    exact List.mem_map.mpr ⟨t.data, hmem_sublists, rfl⟩

end String


namespace String

/-! ## Repeated substring detection -/

/-- Returns true if there exist two distinct positions `i ≠ j` in `s` such that
the substrings of length `len` starting at `i` and `j` are equal. -/
def hasRepeatedSubstringOfLength (s : String) (len : Nat) : Bool :=
  let starts : List Nat := (List.range (s.length + 1)).filter (fun i => i + len ≤ s.length)
  starts.any (fun i =>
    starts.any (fun j =>
      decide (i ≠ j) && decide (s.slice i len = s.slice j len)))

/-- If `len` exceeds the length of `s`, no repeated substring of length `len` can exist. -/
lemma hasRepeatedSubstringOfLength_eq_false_of_lt_length (s : String) (n : Nat) (hlt : s.length < n) :
    hasRepeatedSubstringOfLength s n = false := by
  have h : ∀ i : Nat, ¬ i + n ≤ s.length := by omega
  simp [hasRepeatedSubstringOfLength, h]

/-- Convenience: a repeated substring longer than the string itself is impossible. -/
lemma hasRepeatedSubstringOfLength_boundary (s : String) :
    hasRepeatedSubstringOfLength s (s.length + 1) = false :=
  hasRepeatedSubstringOfLength_eq_false_of_lt_length s (s.length + 1) (by omega)

end String
