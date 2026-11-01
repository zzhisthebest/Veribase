import Mathlib
import general.List.Slicing
import general.List.Transformations
import general.String.CharacterStatistics
import general.String.Substrings
import general.String.Normalization

namespace String

/-! ## All split positions -/

/-- All `(prefix, suffix)` pairs obtained by splitting `s` at every position from `0` to
`s.length`. For example, `allSplits "ab" = [("", "ab"), ("a", "b"), ("ab", "")]`.
This is useful for exhaustive splitting algorithms such as parsing or segment validation. -/
def allSplits (s : String) : List (String × String) :=
  let L := s.length
  (List.range (L + 1)).map (fun i => (s.take i, s.drop i))

/-! ## Split and Join -/

/-- Split a string into words by spaces. -/
def words (s : String) : List String :=
  s.splitOn " "

/-- Count the number of segments after splitting a string by predicate `p`. -/
def countSplit (p : Char → Bool) (s : String) : Nat := (s.split p).length

/-- Split a string by a separator predicate and keep only substrings satisfying a filter predicate. -/
def splitFilter (s : String) (sep : Char → Bool) (keep : String → Bool) : List String :=
  (s.split sep).filter keep

/-- Split a string into word tokens on non-alphanumeric boundaries, filtering empty tokens.
This is a convenience specialization of `splitByPredNonEmpty` with the predicate
`fun c => ¬ c.isAlphanum`. For example, `splitWords "hello, world!" = ["hello", "world"]`. -/
def splitWords (s : String) : List String :=
  splitByPredNonEmpty (fun c => ¬ c.isAlphanum) s

/-- Extract words from a string by grouping consecutive alphabetic characters
and converting each group to a lowercase string. Non-alphabetic characters
(including digits, punctuation, whitespace) are discarded — they act as
word separators.

This differs from `splitWords` (which keeps alphanumeric tokens) and from
`words` (which splits only on spaces). For example:
* `extractWords "Hello, World!" = ["hello", "world"]`
* `extractWords "abc123def" = ["abc", "def"]` (digits act as separators)
* `extractWords "a_man_a_plan" = ["a", "man", "a", "plan"]` -/
def extractWords (s : String) : List String :=
  (List.groupByConsecutive Char.isAlpha s.data).map fun cs => (String.mk cs).toLower

/-- Extract alphabetic words from a string, preserving case. Each maximal contiguous
sequence of alphabetic characters yields one word. Non-alphabetic characters
(including digits, punctuation, whitespace) act as delimiters and are discarded.

This differs from `extractWords` which converts words to lowercase.
For example:
* `extractWordsFromString "Hello, World!" = ["Hello", "World"]`
* `extractWordsFromString "abc123def" = ["abc", "def"]`
* `extractWordsFromString "" = []` -/
def extractWordsFromString (s : String) : List String :=
  List.splitWordsBy (·.isAlpha) s.data


theorem extractWordsFromString_nil : extractWordsFromString "" = [] := by
  first
  | (solve
    | rfl
    | simp_all [extractWordsFromString]
    | omega
    | aesop
    | simp_all [extractWordsFromString, List.foldl, List.foldr]
    | simp_all [extractWordsFromString, Nat.absDiff])

/-- Count the number of non-empty substrings after splitting a string by a predicate.
Equivalent to `(splitByPredNonEmpty p s).length`. -/
def countNonEmptySplit (p : Char → Bool) (s : String) : Nat :=
  (splitByPredNonEmpty p s).length

/-- Count the number of lines in a string, splitting on newline characters. -/
def countLines (s : String) : Nat :=
  countNonEmptySplit (fun c => c == '\n') s

/-- Count the number of words in a string, splitting on whitespace characters.
Whitespace includes space, tab, newline, and carriage return. -/
def countWords (s : String) : Nat :=
  countNonEmptySplit Char.isWhitespace s

/-- Count how many space-separated words in `text` appear in the dictionary `dict`,
case-insensitively (words in `text` are lowered before comparison). The dictionary
should contain lowercase strings for correct matching.

For example:
* `countWordsIn ["hello","world"] "Hello World" = 2`
* `countWordsIn ["hello"] "Hello Hello World" = 2`
* `countWordsIn [] "hello world" = 0` -/
def countWordsIn (dict : List String) (text : String) : Nat :=
  let ws := text.split (fun c => c = ' ')
  List.countP (fun w => w.toLower ∈ dict) ws

/-- Split a string by the given character, discarding empty segments. -/
def splitByCharNonEmpty (c : Char) (s : String) : List String :=
  splitByPredNonEmpty (fun ch => ch == c) s

/-- Split a string on a delimiter predicate and trim whitespace from each segment.
This is the general predicate-based version: it splits `s` wherever `p` holds, then
trims leading and trailing whitespace from each resulting segment.
Unlike `splitByCharTrim`, this does not filter out empty segments — it preserves
them so the caller can decide whether to drop them.

For example, `splitTrim (· = ',') " a , b ,  c  " = ["a", "b", "c"]` but with
empty segments: `splitTrim (· = ',') ",a,," = ["", "a", "", ""]`. -/
def splitTrim (s : String) (p : Char → Bool) : List String :=
  (s.split p).map String.trim

/-- Split a string by the given character, trim each component, and discard empty segments.
This is a variant of `splitByCharNonEmpty` that also trims whitespace from each component.
Useful for processing delimiter-separated text where components may have leading/trailing
whitespace, e.g., path components or comma-separated values.

For example, `splitByCharTrim '/' " /home / user / /docs " = ["home", "user", "docs"]`. -/
def splitByCharTrim (sep : Char) (s : String) : List String :=
  (s.split (fun c => c = sep)).map String.trim
    |>.filter (fun s => s ≠ "")

/-- Split a string on a delimiter predicate, trim whitespace from each segment,
and discard empty segments. This is the predicate-based generalization of
`splitByCharTrim`: unlike `splitByCharTrim` which splits on a single character,
this splits wherever the predicate `p` holds.

For example, `splitTrimNonEmpty (fun c => c = ',' ∨ c = ';') " a ; b ,  c  " = ["a", "b", "c"]`. -/
def splitTrimNonEmpty (s : String) (p : Char → Bool) : List String :=
  ((s.split p).map String.trim).filter (fun s => s ≠ "")

lemma splitTokens_empty : splitTokens "" = [] := by
  have hs : "".split (fun c => c == ' ') = [""] := by
    unfold String.split
    rw [String.splitAux.eq_1]
    simp [String.atEnd]
    rfl
  simp [splitTokens, splitByPredNonEmpty, hs]

lemma splitTokens_eq_splitFilter : splitTokens = (fun s => splitFilter s (· == ' ') (· != "")) := rfl

/-- Lowercase a string and split it into non-empty words by whitespace.
Equivalent to `splitTokens s.toLower`. This is a common preprocessing step
for string comparison and searching problems. -/
def lowerWords (s : String) : List String :=
  splitTokens s.toLower


lemma lowerWords_empty : lowerWords "" = [] := by
  unfold lowerWords String.toLower String.map
  rw [String.mapAux]
  rw [dif_pos (show "".atEnd 0 = true from by decide)]
  exact splitTokens_empty

/-- Lowercase a string, split into words, and sort them lexicographically.
Uses `insertionSort` which is efficient for small collections. -/
def sortedLowerWords (s : String) : List String :=
  (lowerWords s).insertionSort (· ≤ ·)

/-- Split a string by delimiter, or keep it as a singleton if the delimiter is empty.
This is a general-purpose utility: `"".splitOn c` splits into individual characters,
which is usually not the desired behavior when the delimiter is empty.

For example:
* `splitOrKeep "," "a,b,c" = ["a", "b", "c"]`
* `splitOrKeep "" "hello" = ["hello"]` (keeps as singleton, unlike `splitOn "" "hello"`)
* `splitOrKeep " " "hello world" = ["hello", "world"]` -/
def splitOrKeep (delimiter : String) (s : String) : List String :=
  if delimiter = "" then [s] else s.splitOn delimiter

/-- Split a string `s` by `delim`, but return `[]` when `s` is the empty string.
This is a variation of `splitOn` that treats the empty input specially:
`"".splitOn delim` returns `[""]`, but `splitUnlessEmpty delim ""` returns `[]`.

For example:
* `splitUnlessEmpty "," "a,b,c" = ["a", "b", "c"]`
* `splitUnlessEmpty "," "" = []`
* `splitUnlessEmpty "," "hello" = ["hello"]` -/
def splitUnlessEmpty (delim s : String) : List String :=
  if s = "" then [] else s.splitOn delim

/-- Split a string on a separator and retain only non-empty segments. -/
def splitOnNonEmpty (s : String) (sep : String) : List String :=
  List.filterNonEmpty (s.splitOn sep)

theorem splitOnNonEmpty_length_le (s sep : String) :
    (splitOnNonEmpty s sep).length ≤ (s.splitOn sep).length := by
  simp [splitOnNonEmpty, List.filterNonEmpty_length_le]

/-- Split a string by delimiter, apply `f` to each part, and filter out empty strings.
This generalizes `splitOnNonEmpty` (which applies the identity function) and
`splitByCharTrim` (which trims each component after splitting by a character).

For example:
* `splitMapNonEmpty "," String.toLower "A,B,C" = ["a", "b", "c"]`
* `splitMapNonEmpty " " id "hello  world" = ["hello", "world"]` -/
def splitMapNonEmpty (delim : String) (f : String → String) (s : String) : List String :=
  ((s.splitOn delim).map f).filter (fun w => w ≠ "")

/-- Split `content` by `lineSep`, then for each segment whose trimmed form starts with `pfx`,
extract the text after `pfx` up to (but excluding) the first occurrence of `delim`.
This is a general-purpose parser combinator for extracting prefixed fields from structured text.

For example:
* `extractPrefixed "\n" "def " '(' "def foo(x) := ..." = ["foo"]`
* `extractPrefixed "," "name:" ',' "name:alice,name:bob " = ["alice", "bob"]` -/
def extractPrefixed (lineSep pfx : String) (delim : Char) (content : String) : List String :=
  (content.splitOn lineSep).filterMap
    (fun line =>
      let trimmed := line.trim
      if trimmed.take pfx.length = pfx then
        let rest := trimmed.drop pfx.length
        let name := rest.takeWhile (fun c => c ≠ delim)
        some name
      else none)

/-- Reverse a list of strings and join them with a separator string.
Equivalent to `String.intercalate sep (List.reverse ws)`.
For example, `intercalateReverse " " ["world", "hello"] = "hello world"`.

This is a general-purpose join-after-reverse combinator, more primitive than
`reverseParts` (which also splits a source string). -/
def intercalateReverse (sep : String) (ws : List String) : String :=
  String.intercalate sep (List.reverse ws)

/-- Reverse the order of non-empty substrings separated by `sep` in `s`.
Uses `splitOnNonEmpty` to split on the separator and filter out empty segments,
then reverses the resulting non-empty substrings and joins them back with `sep`.

For example, `reverseParts "hello, world, " ", " = "world, hello"`.
This generalizes `reverseWordOrder` (which is `reverseParts s " "`). -/
def reverseParts (s : String) (sep : String) : String :=
  String.intercalate sep (List.reverse (String.splitOnNonEmpty s sep))

/-- `reverseParts s sep` expands to `intercalate sep` of the reverse of the non-empty split. -/
lemma reverseParts_expand (s : String) (sep : String) :
    String.reverseParts s sep = String.intercalate sep (List.reverse (List.filterNonEmpty (s.splitOn sep))) := by
  simp [String.reverseParts, String.splitOnNonEmpty]

/-- Reverse the parts of a string obtained by splitting on separator character `sep`,
then rejoin with the same separator. For example, `reverseSplit ',' "a,b,c"` gives `"c,b,a"`.

This is the character-separator variant of `reverseParts` (which takes a `String` separator).
Unlike `reverseParts`, this does not filter out empty segments — all split results are
preserved and reversed. -/
def reverseSplit (sep : Char) (s : String) : String :=
  let parts := s.split (fun c => c = sep)
  let charLists := parts.map String.data
  String.mk ([sep].intercalate charLists.reverse)

/-- If no word in `ws` contains the separator `sep` and `ws` is non-empty, then
splitting the sep-intercalated reversed char-lists of `ws` on `sep` recovers
the reversed word list. This is the key correctness property of `reverseSplit`. -/
lemma split_reverseSplit_eq (sep : Char) (ws : List String)
    (h_no_sep : ∀ w ∈ ws, sep ∉ w.data) (h_ne_nil : ws ≠ []) :
    (String.mk ([sep].intercalate ((ws.map String.data).reverse))).split (fun c => c = sep) =
    ws.reverse := by
  set p : Char → Bool := fun c => decide (c = sep) with hp
  have h_no_sep_rev : ∀ l ∈ (ws.map String.data).reverse, sep ∉ l := by
    intro l hl
    have hl' : l ∈ ws.map String.data := (List.mem_reverse.mp hl)
    rcases List.mem_map.mp hl' with ⟨w, hw, rfl⟩
    exact h_no_sep w hw
  have h_ls_ne_nil : (ws.map String.data).reverse ≠ [] := by
    intro h
    apply h_ne_nil
    apply (List.map_eq_nil_iff (f := String.data)).mp
    exact (List.reverse_eq_nil_iff.mp h)
  have h_split_intercalate : ([sep].intercalate ((ws.map String.data).reverse)).splitOn sep =
      (ws.map String.data).reverse :=
    List.splitOn_intercalate ((ws.map String.data).reverse) sep h_no_sep_rev h_ls_ne_nil
  rw [String.split_of_valid (String.mk ([sep].intercalate ((ws.map String.data).reverse))) p]
  have h_eq : (ws.map String.data).reverse =
      List.splitOnP p ([sep].intercalate ((ws.map String.data).reverse)) := by
    simpa [hp] using h_split_intercalate.symm
  rw [← h_eq]
  rw [map_mk_data_reverse ws]

/-- Split a string `s` into exactly two parts on separator `sep`.
Returns `some (before, after)` if `s.splitOn sep` yields exactly two strings;
returns `none` if the separator appears zero times or more than once.

For example:
* `splitPairOn "=" "key=value" = some ("key", "value")`
* `splitPairOn "=" "a=b=c" = none` (more than one `=`)
* `splitPairOn "=" "noequal" = none` (no `=`) -/
def splitPairOn (sep : String) (s : String) : Option (String × String) :=
  match s.splitOn sep with
  | [a, b] => some (a, b)
  | _ => none

/-- Split a string `p` around the first occurrence of character `c`.
Returns `some (a, b)` where `a` is the prefix before the first `c` and `b` is
the suffix after it, so that `p = a ++ [c].asString ++ b`. The character `c`
does not occur in `a`.
Returns `none` if `c` is not present in `p`.

For example:
* `splitOnFirstChar '*' "abc*def" = some ("abc", "def")`
* `splitOnFirstChar '*' "abc" = none`
* `splitOnFirstChar ' ' "hello world again" = some ("hello", "world again")` -/
def splitOnFirstChar (c : Char) (p : String) : Option (String × String) :=
  match p.data.findIdx? (· = c) with
  | none => none
  | some idx =>
      let a := String.mk (p.data.take idx)
      let b := String.mk (p.data.drop (idx + 1))
      some (a, b)

/-- Split a string at the first occurrence of a delimiter character `c`, assuming `c`
appears exactly once. If `c` appears exactly once, returns `(before, after)` with
both parts excluding the delimiter; otherwise returns `(s, "")`.

Unlike `splitOnFirstChar` (which splits at the first occurrence and returns an
`Option`), this splits on ALL occurrences via `String.split` then pattern-matches
on exactly-two substrings. Useful when you know there is exactly one delimiter
(e.g., splitting equations on `'='`).

For example:
* `splitAtChar '=' "2x+3=5" = ("2x+3", "5")`
* `splitAtChar '=' "noequal" = ("noequal", "")`
* `splitAtChar '=' "a=b=c" = ("a=b=c", "")` -/
def splitAtChar (c : Char) (s : String) : String × String :=
  match s.split (fun d => d = c) with
  | [l, r] => (l, r)
  | _      => (s, "")

/-- Return the prefix of `s` before the first occurrence of character `c`.
If `c` is not found, return `s` unchanged.

For example:
* `prefixBeforeChar '+' "foo+bar" = "foo"`
* `prefixBeforeChar '.' "localhost" = "localhost"`
* `prefixBeforeChar '@' "user@domain" = "user"` -/
def prefixBeforeChar (c : Char) (s : String) : String :=
  (s.split (fun d => d == c)).headD s

/--
Returns the first field obtained by splitting `s` on the separator character `sep`.
For example, `String.firstField "a;b;c" ';'` returns `"a"`, and if there is no separator,
the entire string is returned.
-/
def firstField (s : String) (sep : Char) : String :=
  (s.split (fun c => c = sep)).head?.getD ""

/-- Extract the prefix of a string before the first occurrence of a string separator.
Returns the whole string if the separator is not found.

This is the `String`-separator version of `prefixBeforeChar` (which handles `Char` separators).
For example:
* `prefixBefore "hello world" " " = "hello"`
* `prefixBefore "hello world" "-" = "hello world"` (separator not found) -/
def prefixBefore (s : String) (sep : String) : String :=
  (s.splitOn sep).head?.getD ""

/-- Extract the suffix of `s` after the last occurrence of separator `sep`.
Returns the empty string if `sep` does not appear in `s`.

This is the complement of `prefixBefore`: `prefixBefore` extracts the substring
before the *first* occurrence of `sep`, while `afterLast` extracts the substring
after the *last* occurrence.

For example:
* `afterLast "." "foo.bar.txt" = "txt"` (last period)
* `afterLast "." "Makefile" = ""` (no period)
* `afterLast "/" "a/b/c" = "c"` (last directory in path) -/
def afterLast (sep s : String) : String :=
  match s.splitOn sep with
  | []      => ""
  | parts   => parts.getLastD ""

/-- Join a list of strings with a separator.
Defined recursively for easier induction, equivalent to `String.intercalate`.
`joinWith sep [] = ""`, `joinWith sep [w] = w`,
and `joinWith sep (w :: w' :: ws) = w ++ sep ++ joinWith sep (w' :: ws)`. -/
def joinWith (sep : String) : List String → String
  | [] => ""
  | [w] => w
  | w :: ws => w ++ sep ++ joinWith sep ws

/-- Join a list of strings with newline separators, with a trailing newline after the
last element. For a version without trailing newline, use `joinWith "\n"`.
For example, `joinWithNewline ["a", "b"] = "a\nb\n"`. -/
def joinWithNewline (ss : List String) : String :=
  List.foldr (fun s acc => s ++ "\n" ++ acc) "" ss

/-- Join a list of strings with a single space between each adjacent pair.
Equivalent to `String.intercalate " " ws`.

For example:
* `joinWithSpaces [] = ""`
* `joinWithSpaces ["hello"] = "hello"`
* `joinWithSpaces ["hello", "world"] = "hello world"` -/
def joinWithSpaces : List String → String
  | []        => ""
  | [s]       => s
  | s :: rest => s ++ " " ++ joinWithSpaces rest

/-- Join a list of strings into a single string with spaces, filtering out empty strings.
The inverse of `splitTokens` (which splits on spaces and filters empties).
For example, `joinWords ["hello", "", "world"] = "hello world"`. -/
def joinWords (ls : List String) : String :=
  String.intercalate " " (ls.filter fun s => s ≠ "")

/-- Count the number of non-empty strings in a list.
For example, `countNonEmpty ["a", "", "b", "", "c"] = 3`. -/
def countNonEmpty (strings : List String) : Nat :=
  (strings.filter (fun str => str ≠ "")).length


lemma countNonEmpty_nil : countNonEmpty [] = 0 := rfl

lemma countNonEmpty_cons (s : String) (ss : List String) :
    countNonEmpty (s :: ss) = (if s = "" then 0 else 1) + countNonEmpty ss := by
  unfold countNonEmpty
  by_cases h : s = ""
  · simp [h]
  · simp [h]; omega

lemma countNonEmpty_append (ws₁ ws₂ : List String) :
    countNonEmpty (ws₁ ++ ws₂) = countNonEmpty ws₁ + countNonEmpty ws₂ := by
  simp [countNonEmpty]


lemma countNonEmpty_cons_empty (ws : List String) :
    countNonEmpty ("" :: ws) = countNonEmpty ws := by
  simp [countNonEmpty]

lemma countNonEmpty_cons_ne_empty (w : String) (ws : List String) (hw : w ≠ "") :
    countNonEmpty (w :: ws) = countNonEmpty ws + 1 := by
  simp [countNonEmpty, hw]

end String

namespace String


/-! ## `String.intercalate` lemmas -/

/-- The base case of `String.intercalate.go`: when the list is empty, the accumulator
is returned as-is. This is a fundamental unfolding lemma. -/
lemma intercalate_go_nil (acc sep : String) : String.intercalate.go acc sep [] = acc := by
  simp [String.intercalate.go]

/-- The inductive step of `String.intercalate.go`: processing `a :: as` prepends the
separator and `a` to the accumulator and recurses. This is a fundamental unfolding lemma. -/
lemma intercalate_go_cons (acc sep a : String) (as : List String) :
    String.intercalate.go acc sep (a :: as) = String.intercalate.go (acc ++ sep ++ a) sep as := by
  simp [String.intercalate.go]

/-- Key lemma: `intercalate.go (acc ++ s) sep ws = acc ++ intercalate.go s sep ws`.
This captures the associativity of the accumulator in `String.intercalate`. -/
lemma intercalate_go_append (acc s sep : String) (ws : List String) :
    String.intercalate.go (acc ++ s) sep ws = acc ++ String.intercalate.go s sep ws := by
  induction' ws with w ws ih generalizing acc s
  · rfl
  · simp [String.intercalate.go, String.append_assoc, ih]

/-- One-step expansion of `intercalate.go` into concatenation form:
`String.intercalate.go a sep (b :: bs) = a ++ sep ++ String.intercalate sep (b :: bs)`.
This is more convenient than the definitional unfolding `intercalate_go_cons`
when reasoning about the relationship between `go` and `intercalate`. -/
lemma intercalate_go_cons_expand (a b : String) (sep : String) (bs : List String) :
    String.intercalate.go a sep (b :: bs) = a ++ sep ++ String.intercalate sep (b :: bs) := by
  induction bs generalizing a b with
  | nil => simp [String.intercalate, String.intercalate.go]
  | cons c cs ih =>
    calc
      String.intercalate.go a sep (b :: c :: cs) =
          String.intercalate.go (a ++ sep ++ b) sep (c :: cs) := rfl
      _ = (a ++ sep ++ b) ++ sep ++ String.intercalate sep (c :: cs) := by
        rw [ih (a ++ sep ++ b) c]
      _ = a ++ sep ++ (b ++ sep ++ String.intercalate sep (c :: cs)) := by
        simp [String.append_assoc]
      _ = a ++ sep ++ (String.intercalate.go b sep (c :: cs)) := by rw [ih b c]
      _ = a ++ sep ++ String.intercalate sep (b :: c :: cs) := rfl

/-- `String.intercalate sep ("" :: w :: ws) = sep ++ String.intercalate sep (w :: ws)`. -/
lemma intercalate_nil_cons (sep : String) (w : String) (ws : List String) :
    String.intercalate sep ("" :: w :: ws) = sep ++ String.intercalate sep (w :: ws) := by
  simp [String.intercalate]
  rw [show String.intercalate.go "" sep (w :: ws) =
      String.intercalate.go ("" ++ sep ++ w) sep ws from rfl]
  simp [intercalate_go_append]

/-- `String.intercalate sep ((s ++ w) :: ws) = s ++ String.intercalate sep (w :: ws)`. -/
lemma intercalate_cons_prepend (s sep w : String) (ws : List String) :
    String.intercalate sep ((s ++ w) :: ws) = s ++ String.intercalate sep (w :: ws) := by
  simp [String.intercalate, intercalate_go_append]

/-- Intercalating an empty list returns the empty string:
`String.intercalate sep [] = ""`. This is the base case for
intercalation. -/

lemma intercalate_nil (sep : String) : String.intercalate sep [] = "" := rfl

/-- The length of `String.intercalate sep []` is zero. -/

lemma length_intercalate_nil (sep : String) : (String.intercalate sep []).length = 0 := by
  first
  | (solve
    | rfl
    | simp_all []
    | omega
    | aesop
    | simp_all [List.foldl, List.foldr]
    | simp_all [Nat.absDiff])

/-- Length of `String.intercalate.go` for any separator and accumulator.
The total length is the accumulator length plus `sep.length` for each element
plus the sum of element lengths. -/
lemma length_intercalate_go_sep (a : String) (sep : String) (l : List String) :
    (String.intercalate.go a sep l).length = a.length + sep.length * l.length +
    ((l.map String.length).sum : ℕ) := by
  induction l generalizing a with
  | nil => simp [String.intercalate.go]
  | cons b bs ih =>
    have hgo : String.intercalate.go a sep (b :: bs) =
        String.intercalate.go (a ++ sep ++ b) sep bs := rfl
    rw [hgo]
    rw [ih (a ++ sep ++ b)]
    have hlen_append : (a ++ sep ++ b).length = a.length + sep.length + b.length := by
      simp [String.length_append]
    have hbs_len : (b :: bs).length = bs.length + 1 := by simp
    have hsum : ((b :: bs).map String.length).sum =
        b.length + ((bs.map String.length).sum) := by simp
    have h_mul : sep.length * (bs.length + 1) = sep.length * bs.length + sep.length := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [hlen_append, hbs_len, hsum, h_mul]
    omega

/-- Length of `String.intercalate sep` for a non-empty list.
The length is the sum of element lengths plus `sep.length * (length - 1)`. -/
lemma length_intercalate_nonempty (l : List String) (sep : String) (hne : l ≠ []) :
    (String.intercalate sep l).length =
    ((l.map String.length).sum : ℕ) + sep.length * (l.length - 1) := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons w ws =>
    have hgo : String.intercalate sep (w :: ws) =
        String.intercalate.go w sep ws := by simp [String.intercalate]
    rw [hgo]
    rw [length_intercalate_go_sep w sep ws]
    have hsum : ((w :: ws).map String.length).sum =
        w.length + ((ws.map String.length).sum) := by simp
    have hlen : (w :: ws).length = ws.length + 1 := by simp
    have h_sub : (ws.length + 1 - 1) = ws.length := by omega
    rw [hsum, hlen, h_sub]
    omega

/-- Intercalating a singleton list just returns the element:
`String.intercalate sep [x] = x`. This is a key simplification for
single-element intercalations. -/

lemma intercalate_singleton (sep x : String) : String.intercalate sep [x] = x := rfl

/-- Unfolding `String.intercalate` on a list with at least two elements:
`String.intercalate s (a :: b :: bs) = a ++ s ++ String.intercalate s (b :: bs)`. -/
lemma intercalate_cons' (s a b : String) (bs : List String) :
    String.intercalate s (a :: b :: bs) = a ++ s ++ String.intercalate s (b :: bs) := by
  simp [String.intercalate, intercalate_go_cons, intercalate_go_append]

/-- Unfolding `String.intercalate` on a cons list:
if `ws` is empty, the result is `a`; otherwise it prepends `a ++ s`.
This unifies `intercalate_singleton` and `intercalate_cons'` into a single lemma. -/
lemma intercalate_cons (s a : String) (ws : List String) :
    String.intercalate s (a :: ws) =
    if ws.isEmpty then a
    else a ++ s ++ String.intercalate s ws := by
  cases ws with
  | nil => rfl
  | cons b bs => simpa using intercalate_cons' s a b bs

/-- The character data of `String.intercalate s l` equals
`List.intercalate s.data (l.map String.data)`. This bridges string and list
intercalation at the data level. -/
lemma data_intercalate (s : String) (l : List String) :
    (String.intercalate s l).data = List.intercalate s.data (l.map String.data) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil =>
      simp [String.intercalate, intercalate_go_nil, List.intercalate]
    | cons b bs =>
      rw [intercalate_cons' s a b bs]
      calc
        (a ++ s ++ String.intercalate s (b :: bs)).data
            = a.data ++ s.data ++ (String.intercalate s (b :: bs)).data := by
              simp [String.data_append]
        _ = a.data ++ s.data ++ List.intercalate s.data
              (List.map String.data (b :: bs)) := by rw [ih]
        _ = a.data ++ s.data ++ List.intercalate s.data
              (b.data :: List.map String.data bs) := rfl
        _ = List.intercalate s.data
              (a.data :: b.data :: List.map String.data bs) := by
              simp [List.intercalate, List.flatten]
        _ = List.intercalate s.data (List.map String.data (a :: b :: bs)) := rfl

/-- `String.intercalate s ws` is equal to `String.join (List.intersperse s ws)`.
This relates `String.intercalate` (which uses `String.intercalate.go` internally) to
the simpler `String.join`-of-`List.intersperse` formulation. For example,
`String.intercalate ", " ["a", "b", "c"] = String.join ["a", ", ", "b", ", ", "c"]`. -/
lemma intercalate_eq_join_intersperse (s : String) (ws : List String) :
    String.intercalate s ws = String.join (List.intersperse s ws) := by
  have shift (l : List String) (a b : String) :
      l.foldl (fun r t => r ++ t) (a ++ b) = a ++ l.foldl (fun r t => r ++ t) b := by
    induction l generalizing b with
    | nil => rfl
    | cons x xs ih => simpa only [List.foldl_cons, String.append_assoc] using ih (b ++ x)
  have cons (a : String) (l : List String) : String.join (a :: l) = a ++ String.join l := by
    simpa [String.join] using shift l a ""
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    cases ws with
    | nil => simp [String.intercalate, String.intercalate.go, String.join]
    | cons b bs => rw [intercalate_cons', List.intersperse_cons₂, cons, cons, ← ih, String.append_assoc]

/-! ### `intercalateWithPrefix` — prepend separator before intercalated list -/

/-- Intercalate a list of strings with a separator, prepending the separator at the beginning.
`intercalateWithPrefix sep [a, b, c] = sep ++ a ++ sep ++ b ++ sep ++ c`.
This is useful when building path-like strings that start with a delimiter,
e.g., constructing an absolute path from directory components.

For example, `intercalateWithPrefix "/" ["home", "user", "docs"] = "/home/user/docs"`. -/
def intercalateWithPrefix (sep : String) (comps : List String) : String :=
  sep ++ String.intercalate sep comps


lemma intercalateWithPrefix_nil (sep : String) : intercalateWithPrefix sep [] = sep := by
  unfold intercalateWithPrefix String.intercalate
  simp

/-! ### `intercalateMap` — apply a function then intercalate -/

/-- `intercalateMap sep f l` applies `f` to each element of `l` and joins the results
with separator `sep`. This is `String.intercalate sep (l.map f)`. -/
def intercalateMap (sep : String) (f : α → String) (l : List α) : String :=
  String.intercalate sep (l.map f)

/-- Intercalating the mapped results of an empty list returns the empty string. -/

theorem intercalateMap_nil (sep : String) (f : α → String) :
    intercalateMap sep f [] = "" := rfl

/-- Intercalating the mapped result of a singleton list returns the result of applying `f`
to the single element. -/
theorem intercalateMap_singleton (sep : String) (f : α → String) (x : α) :
    intercalateMap sep f [x] = f x := by
  first
  | (solve
    | rfl
    | simp_all [intercalateMap]
    | omega
    | aesop
    | simp_all [intercalateMap, List.foldl, List.foldr]
    | simp_all [intercalateMap, Nat.absDiff])

/-! ### `splitMapJoin` — split by predicate, map, then join -/

/-- Map a function over substrings obtained by splitting on a predicate,
then join the mapped results with a separator string.

This generalizes `mapWords` (which splits on a single character) and
`mapDelimited` (which trims each segment). Equivalent to
`intercalateMap sep f (s.split p)`.

For example:
* `splitMapJoin id (· = ',') ", " "a,b,c" = "a, b, c"`
* `splitMapJoin String.reverse (· = ' ') "-" "hello world" = "olleh-dlrow"` -/
def splitMapJoin (f : String → String) (p : Char → Bool) (sep : String) (s : String) : String :=
  String.intercalate sep ((s.split p).map f)

/-! ## `wordsOfChars` — split `List Char` on a separator -/

/-- Extract delimiter-separated words from a character list as strings.
Always returns a non-empty list of strings (at minimum `[""]`).
For example, `wordsOfChars ' ' ['h','e','l','l','o',' ','w','o','r','l','d'] = ["hello", "world"]`. -/
def wordsOfChars (sep : Char) : List Char → List String
  | [] => [""]
  | c :: rest =>
    if c = sep then
      "" :: wordsOfChars sep rest
    else
      match wordsOfChars sep rest with
      | w :: ws => (String.singleton c ++ w) :: ws
      | [] => [String.singleton c]

/-- `wordsOfChars sep cs` always produces a non-empty list. -/
lemma wordsOfChars_ne_nil (sep : Char) (cs : List Char) : wordsOfChars sep cs ≠ [] := by
  induction' cs with c cs ih
  · simp [wordsOfChars]
  · by_cases hc : c = sep
    · subst hc; simp [wordsOfChars]
    · simp [wordsOfChars, hc]
      split <;> simp

/-- `wordsOfChars sep cs` decomposes as `w :: ws` for some `w, ws`. -/
lemma wordsOfChars_cons (sep : Char) (cs : List Char) :
    ∃ w ws, wordsOfChars sep cs = w :: ws := by
  have h_ne := wordsOfChars_ne_nil sep cs
  cases h' : wordsOfChars sep cs with
  | nil => exfalso; exact h_ne h'
  | cons w ws => exact ⟨w, ws, rfl⟩

/-- `wordsOfChars sep` correctly reconstructs the original string via `String.intercalate`. -/
lemma intercalate_wordsOfChars_eq (sep : Char) (cs : List Char) :
    String.intercalate (String.singleton sep) (wordsOfChars sep cs) = String.mk cs := by
  induction' cs with c cs ih
  · rfl
  · rcases wordsOfChars_cons sep cs with ⟨w, ws, h_cons⟩
    rw [h_cons] at ih
    by_cases hc : c = sep
    · simp [wordsOfChars, hc, h_cons]
      rw [intercalate_nil_cons (String.singleton sep) w ws, ih]
      apply String.ext; simp
    · have h_woc : wordsOfChars sep (c :: cs) = (String.singleton c ++ w) :: ws := by
        simp [wordsOfChars, hc, h_cons]
      rw [h_woc]
      rw [intercalate_cons_prepend (String.singleton c) (String.singleton sep) w ws, ih]
      apply String.ext; simp

end String

namespace String

end String

namespace String



lemma joinWith_nil (sep : String) : joinWith sep [] = "" := rfl


lemma joinWith_singleton (sep : String) (w : String) : joinWith sep [w] = w := rfl

/-- `String.join` of the empty list is the empty string. -/

lemma join_nil : String.join ([] : List String) = "" := rfl

/-- `String.join` distributes over `::`: joining a list with head `s` is the same as
concatenating `s` with the join of the tail. This is the fundamental unfolding lemma
for `String.join` on a cons list. -/
lemma join_cons (s : String) (l : List String) : String.join (s :: l) = s ++ String.join l := by
  unfold String.join
  simp [List.foldl]
  induction l generalizing s with
  | nil => simp
  | cons t rest ih =>
    simp [List.foldl]
    rw [ih (s ++ t), ih t, String.append_assoc]

/-- `String.join` distributes over list append:
joining two lists concatenated is the same as concatenating their joins. -/
lemma join_append (l1 l2 : List String) : String.join (l1 ++ l2) = String.join l1 ++ String.join l2 := by
  first
  | (solve
    | rfl
    | simp_all []
    | omega
    | aesop
    | simp_all [List.foldl, List.foldr]
    | simp_all [Nat.absDiff])

/-- `String.join` of a singleton list is the string itself. -/

lemma join_singleton (s : String) : String.join [s] = s := by
  simp [join_cons, join_nil]

/-- `String.join` of `List.intersperse d [s]` is just `s`, since interspersing
a separator into a singleton list has no effect. -/

lemma join_intersperse_single (s d : String) : String.join (List.intersperse d [s]) = s := by
  simp [join_singleton]

/-- Join a list of character lists into a single string, separated by `sep`.
Each inner `List Char` is converted to a `String` via `String.mk`, then all are
interspersed with `sep` and concatenated. -/
def joinBlocksWith (sep : String) (blocks : List (List Char)) : String :=
  String.join (List.intersperse sep (blocks.map String.mk))


lemma joinBlocksWith_nil (sep : String) : joinBlocksWith sep [] = "" :=
  rfl


/-! ### Interleave lists of strings via zip and concatenation -/

/-- Interleave two lists of strings by zipping with append then folding the result.
`interleave [w₁, w₂] [p₁, p₂] = w₁ ++ p₁ ++ w₂ ++ p₂`.
For example, `interleave ["Hello", "World"] [",", "!"] = "Hello,World!"`.

This is the operation that reconstructs a string from interleaved word and
punctuation/wildcard lists in text-processing problems. -/
def interleave (ws pw : List String) : String :=
  (List.zipWith (· ++ ·) ws pw).foldl (· ++ ·) ""


lemma interleave_nil_left (pw : List String) : interleave [] pw = "" := by
  simp [interleave]


lemma interleave_nil_right (ws : List String) : interleave ws [] = "" := by
  simp [interleave]


lemma interleave_nil_nil : interleave [] [] = "" := by
  first
  | (solve
    | rfl
    | simp_all [interleave]
    | omega
    | aesop
    | simp_all [interleave, List.foldl, List.foldr]
    | simp_all [interleave, Nat.absDiff])

lemma interleave_cons_cons (w p : String) (ws pw : List String) :
    interleave (w :: ws) (p :: pw) = w ++ p ++ interleave ws pw := by
  unfold interleave
  have hzip : List.zipWith (· ++ ·) (w :: ws) (p :: pw) = (w ++ p) :: List.zipWith (· ++ ·) ws pw := rfl
  have hfold : (((w ++ p) :: List.zipWith (· ++ ·) ws pw).foldl (· ++ ·) "") =
      (List.zipWith (· ++ ·) ws pw).foldl (· ++ ·) (w ++ p) := rfl
  rw [hzip, hfold]
  rw [List.foldl_append_init (w ++ p) (List.zipWith (· ++ ·) ws pw)]
  rfl


end String

namespace String

/-! # Join a pair of strings with a separator

`joinWithSep sep a b` joins two strings `a` and `b` with `sep` between them.
For example: `joinWithSep "/" "usr" "bin" = "usr/bin"`. -/

/-- Join two strings with a separator: `a ++ sep ++ b`. -/
def joinWithSep (sep a b : String) : String :=
  a ++ sep ++ b

/-- The length of `joinWithSep sep a b` is the sum of the lengths. -/

lemma joinWithSep_length (sep a b : String) : (joinWithSep sep a b).length = a.length + sep.length + b.length := by
  simp [joinWithSep]

/-! # Map-and-join: combine character mapping with separator joining

`mapJoin sep f s` maps each character `c` in `s` via `f : Char → String` and joins
the results with separator `sep`. This is a common pattern that combines `String.intercalate`
with character mapping in a single pass.

For example: `mapJoin ", " (fun c => toString (Char.toNat c)) "abc" = "97, 98, 99"`.
-/

/-- Map each character `c` in `s` via `f : Char → String` and join the results with
separator `sep`. Equivalent to `String.intercalate sep (s.data.map f)`. -/
def mapJoin (sep : String) (f : Char → String) (s : String) : String :=
  String.intercalate sep (s.data.map f)

/-! # `joinToString` — join a list without a separator using `ToString`

`joinToString xs` converts each element to a string via `ToString` and concatenates
them. This is the simplest `ToString`-based join: no separator between elements,
unlike `joinSep` which adds a `sep` between each pair.

Main equations:
* `joinToString [] = ""`
-/

/-- Join a list of values into a `String` by converting each element via `toString` and
concatenating the results. No separator is inserted between elements.

For example: `joinToString ([1, 2, 3] : List Nat) = "123"`. -/
def joinToString [ToString α] (xs : List α) : String :=
  xs.foldl (fun s x => s ++ toString x) ""


theorem joinToString_nil {α : Type} [ToString α] : joinToString ([] : List α) = "" := by
  simp [joinToString]

/-! # `joinSep` — join a list with a separator using `ToString`

`joinSep sep list` converts each element to a string via `ToString` and joins
them with `sep` between adjacent elements. This is the `String` analog of
`List.intercalate` generalized to any `ToString` type.

Main equations:
* `joinSep sep [] = ""`
* `joinSep sep [x] = toString x`
* `joinSep sep (x :: y :: zs) = toString x ++ sep ++ joinSep sep (y :: zs)`
-/

/-- Join a list of values into a `String`, separating adjacent elements with `sep`.
Each element is converted to a string via `toString`.

For example: `joinSep ", " ([1, 2, 3] : List Nat) = "1, 2, 3"`. -/
def joinSep [ToString α] (sep : String) : List α → String
  | []      => ""
  | [x]     => toString x
  | x :: xs => toString x ++ sep ++ joinSep sep xs


lemma joinSep_nil [ToString α] (sep : String) : joinSep sep ([] : List α) = "" := rfl


lemma joinSep_singleton [ToString α] (sep : String) (x : α) : joinSep sep [x] = toString x := rfl

/-- `joinSep` on a list with at least two elements expands to the first element,
the separator, and the join of the rest. -/
lemma joinSep_cons [ToString α] (sep : String) (x : α) (y : α) (zs : List α) :
    joinSep sep (x :: y :: zs) = toString x ++ sep ++ joinSep sep (y :: zs) := rfl

/-- `joinSep` on a list reduces to `String.intercalate` on the list of `toString`-ed elements. -/
lemma joinSep_eq_intercalate [ToString α] (sep : String) (l : List α) :
    joinSep sep l = String.intercalate sep (l.map toString) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [joinSep_cons, List.map_cons, String.intercalate, String.intercalate.go]
      have h_go : ∀ (a b : String) (ws : List String),
          String.intercalate.go (a ++ sep ++ b) sep ws = a ++ sep ++ String.intercalate.go b sep ws := by
        intro a b ws
        induction ws generalizing a b with
        | nil => rfl
        | cons w ws ih_go =>
          simp only [String.intercalate.go]
          have : (a ++ sep ++ b) ++ sep ++ w = a ++ sep ++ (b ++ sep ++ w) := by
            simp [String.append_assoc]
          rw [this]
          rw [ih_go a (b ++ sep ++ w)]
      calc
        toString x ++ sep ++ joinSep sep (y :: ys)
            = toString x ++ sep ++ String.intercalate sep ((y :: ys).map toString) := by rw [ih]
        _ = toString x ++ sep ++ String.intercalate.go (toString y) sep (List.map toString ys) := rfl
        _ = String.intercalate.go (toString x ++ sep ++ toString y) sep (List.map toString ys) := by
          rw [h_go (toString x) (toString y) (List.map toString ys)]

/-! # `joinOnChar` — join a list of strings with a character separator

`joinOnChar ws sep` joins a list of strings using `sep` as the separator character.
This is a convenience wrapper around `String.intercalate (String.singleton sep)`.
The name mirrors `splitOnChar` in `String/Split.lean`, providing the inverse operation.

Main equations:
* `joinOnChar [] sep = ""`
* `joinOnChar [w] sep = w`
* `joinOnChar (a :: b :: ws) sep = a ++ String.singleton sep ++ joinOnChar (b :: ws) sep`
-/

/-- Join a list of strings with a single-character separator.
Equivalent to `String.intercalate (String.singleton sep) ws`.
The counterpart of `splitOnChar`. For example,
`joinOnChar ["a", "b", "c"] ',' = "a,b,c"`. -/
def joinOnChar (ws : List String) (sep : Char) : String :=
  String.intercalate (String.singleton sep) ws


lemma joinOnChar_nil (sep : Char) : joinOnChar [] sep = "" := by
  first
  | (solve
    | rfl
    | simp_all [joinOnChar]
    | omega
    | aesop
    | simp_all [joinOnChar, List.foldl, List.foldr]
    | simp_all [joinOnChar, Nat.absDiff])


lemma joinOnChar_singleton (w : String) (sep : Char) : joinOnChar [w] sep = w := by
  simp [joinOnChar, String.intercalate, String.intercalate.go]

/-- The length of `joinOnChar (acc ++ [w]) sep` equals the length of `joinOnChar acc sep`
plus (1 if `acc` is nonempty) plus `w.length`. -/
lemma joinOnChar_append_singleton_length (acc : List String) (w : String) (sep : Char) :
    String.length (joinOnChar (acc ++ [w]) sep) =
    String.length (joinOnChar acc sep) + (if acc.isEmpty then 0 else 1) + w.length := by
  cases acc with
  | nil => simp [joinOnChar, String.intercalate, String.intercalate.go]
  | cons a as =>
    unfold joinOnChar
    rw [length_intercalate_nonempty _ _ (by simp), length_intercalate_nonempty _ _ (by simp)]
    simp
    omega

/-! # Theorems about `joinWith`

`joinWith sep ws` joins a list of strings using `sep` between adjacent elements.
Defined in `general.String`. This section collects lemmas about its behavior.

Main equations:
* `joinWith sep [] = ""`
* `joinWith sep [w] = w`
* `joinWith sep (w :: w' :: ws) = w ++ sep ++ joinWith sep (w' :: ws)`
-/

/-- Unfolding `joinWith` for a list with at least two elements. -/
lemma joinWith_cons_two (sep : String) (w w' : String) (ws : List String) :
    joinWith sep (w :: w' :: ws) = w ++ sep ++ joinWith sep (w' :: ws) := rfl

/-- `joinWith` is equivalent to `String.intercalate`. -/
lemma joinWith_eq_intercalate (sep : String) (ws : List String) : joinWith sep ws = String.intercalate sep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases ws with
    | nil => rfl
    | cons w' ws' =>
      simp [joinWith, String.intercalate]
      have h_go : String.intercalate.go w sep (w' :: ws') =
          String.intercalate.go (w ++ sep ++ w') sep ws' := by
        simp [String.intercalate.go]
      rw [h_go]
      have h_append : String.intercalate.go (w ++ sep ++ w') sep ws' =
          (w ++ sep) ++ String.intercalate.go w' sep ws' := by
        calc
          String.intercalate.go (w ++ sep ++ w') sep ws'
              = String.intercalate.go ((w ++ sep) ++ w') sep ws' := by
            simp [String.append_assoc]
          _ = (w ++ sep) ++ String.intercalate.go w' sep ws' :=
            intercalate_go_append (w ++ sep) w' sep ws'
      rw [h_append]
      simp [String.append_assoc]
      have h_inter : String.intercalate sep (w' :: ws') = String.intercalate.go w' sep ws' := by
        simp [String.intercalate]
      rw [← h_inter]
      rw [ih]

/-- `joinWith` of a non-empty list of non-empty strings is non-empty. -/
lemma joinWith_ne_nil (sep : String) (ws : List String) (hnil : ws ≠ []) (hne : ∀ w ∈ ws, w ≠ "") :
    joinWith sep ws ≠ "" := by
  rcases List.exists_cons_of_ne_nil hnil with ⟨w, ws', hws⟩
  subst hws
  have hw_ne : w ≠ "" := hne w (by simp)
  have hw_pos : 0 < String.length w := by
    have h_data : w.data ≠ [] := by
      intro h; apply hw_ne; exact String.ext (by simp [h])
    simpa using List.length_pos_iff.mpr h_data
  cases ws' with
  | nil => simp [joinWith, hw_ne]
  | cons w' ws'' =>
    rw [joinWith_cons_two sep w w' ws'']
    intro h_eq
    have h_len : w.length ≤ (w ++ sep ++ joinWith sep (w' :: ws'')).length := by
      calc
        w.length ≤ (w ++ sep).length := by simp
        _ ≤ (w ++ sep ++ joinWith sep (w' :: ws'')).length := by simp
    rw [h_eq] at h_len
    simp at h_len
    omega

/-! # `joinPairs` — join a list of string pairs with pair- and list-separators

`joinPairs pairSep listSep ps` maps each pair `(a, b)` in `ps` to `a ++ pairSep ++ b`
(using `joinWithSep`) and joins the results with `listSep`. This is useful for
formatting key-value lists, e.g.,
`joinPairs "=" "&" [("name", "John"), ("age", "30")] = "name=John&age=30"`.

Main equations:
* `joinPairs pairSep listSep [] = ""`
-/

/-- Join a list of string pairs using `pairSep` within each pair and `listSep` between pairs. -/
def joinPairs (pairSep listSep : String) (ps : List (String × String)) : String :=
  String.intercalate listSep (ps.map (λ p => joinWithSep pairSep p.fst p.snd))


lemma joinPairs_nil (pairSep listSep : String) : joinPairs pairSep listSep [] = "" := rfl

/-! # `joinSep` snoc lemmas (specialized to `List String`)

These lemmas describe the behavior of `joinSep` when appending to the end of the
list (the "snoc" operation). They are specialized to `List String` because the
right-hand sides involve direct string concatenation.

Main equations:
* `joinSep_snoc_append sep xs y s` — adding a suffix `s` to the last element `y`
  extends the joined result by `s`
* `joinSep_snoc_empty sep xs h` — appending an empty element adds a trailing
  separator, provided the list is nonempty
* `joinSep_snoc_push sep xs cur c` — pushing a character onto the last element
  extends the joined result by `String.singleton c`
-/

/-- Adding a suffix `s` to the last element `y` of the list extends the joined
result by `s`. Formally: `joinSep sep (xs ++ [y ++ s]) = joinSep sep (xs ++ [y]) ++ s`. -/
lemma joinSep_snoc_append (sep : String) (xs : List String) (y s : String) :
    joinSep sep (xs ++ [y ++ s]) = joinSep sep (xs ++ [y]) ++ s := by
  have hts : ∀ (s' : String), toString s' = s' := λ _ => rfl
  induction xs generalizing y s with
  | nil => simp [joinSep, hts]
  | cons x xs ih =>
    cases xs with
    | nil => simp [joinSep, hts, String.append_assoc]
    | cons x' xs' =>
      have h_ih := ih y s
      -- Goal: joinSep sep ((x :: x' :: xs') ++ [y ++ s]) = joinSep sep ((x :: x' :: xs') ++ [y]) ++ s
      -- h_ih: joinSep sep ((x' :: xs') ++ [y ++ s]) = joinSep sep ((x' :: xs') ++ [y]) ++ s
      rw [List.cons_append x (x' :: xs') [y ++ s], List.cons_append x (x' :: xs') [y],
        List.cons_append x' xs' [y ++ s], List.cons_append x' xs' [y]]
      rw [List.cons_append x' xs' [y ++ s], List.cons_append x' xs' [y]] at h_ih
      rw [joinSep_cons sep x x' (xs' ++ [y ++ s]), joinSep_cons sep x x' (xs' ++ [y])]
      simp [hts]
      rw [h_ih]
      rw [← String.append_assoc (x ++ sep) (joinSep sep (x' :: (xs' ++ [y]))) s]

/-- Appending an empty element to a nonempty list adds a trailing separator.
Formally: if `xs ≠ []`, then `joinSep sep (xs ++ [""]) = joinSep sep xs ++ sep`. -/
lemma joinSep_snoc_empty (sep : String) (xs : List String) (h : xs ≠ []) :
    joinSep sep (xs ++ [""]) = joinSep sep xs ++ sep := by
  have hts : ∀ (s' : String), toString s' = s' := λ _ => rfl
  cases' xs with x xs
  · contradiction
  · induction xs generalizing x with
    | nil => simp [joinSep, hts, String.append_empty]
    | cons y ys ih =>
      have h_ih : joinSep sep (y :: ys ++ [""]) = joinSep sep (y :: ys) ++ sep := ih y (by simp)
      -- Goal: joinSep sep ((x :: y :: ys) ++ [""]) = joinSep sep (x :: y :: ys) ++ sep
      -- h_ih: joinSep sep ((y :: ys) ++ [""]) = joinSep sep (y :: ys) ++ sep
      rw [List.cons_append x (y :: ys) [""], List.cons_append y ys [""]]
      rw [List.cons_append y ys [""]] at h_ih
      rw [joinSep_cons sep x y (ys ++ [""]), joinSep_cons sep x y ys]
      simp [hts]
      rw [h_ih]
      rw [← String.append_assoc (x ++ sep) (joinSep sep (y :: ys)) sep]

/-- Pushing a character `c` onto the last element `cur` of the list extends the joined
result by `String.singleton c`. Formally:
`joinSep sep (xs ++ [cur.push c]) = joinSep sep (xs ++ [cur]) ++ String.singleton c`. -/
lemma joinSep_snoc_push (sep : String) (xs : List String) (cur : String) (c : Char) :
    joinSep sep (xs ++ [cur.push c]) = joinSep sep (xs ++ [cur]) ++ String.singleton c := by
  have hts : ∀ (s' : String), toString s' = s' := λ _ => rfl
  simpa [String.push, hts] using joinSep_snoc_append sep xs cur (String.singleton c)

end String

namespace String

/-! ## Foldl append accumulator lemmas -/

/-- `foldl` with `(++)` starting from `""` equals `String.join`.
In other words, `foldlAppend` over a list of strings is the same as `String.join`. -/
lemma foldl_append_eq_join (ws : List String) :
    ws.foldl (fun acc w => acc ++ w) "" = String.join ws := by
  simp [String.join]

/-- The length of a left-fold concatenating strings is the initial length plus the sum of mapped lengths. -/
lemma foldl_append_length {α : Type} (l : List α) (f : α → String) (init : String) :
    (l.foldl (fun acc x => acc ++ f x) init).length =
    init.length + (l.map (fun x => (f x).length)).sum := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp [List.foldl, ih, String.length_append]
    omega

/-- The accumulator at the beginning of a left fold with `(++)` is equivalent to
prepending it to the result of folding with the empty string. -/
lemma foldl_append_acc (ws : List String) (acc : String) :
    List.foldl (· ++ ·) acc ws = acc ++ List.foldl (· ++ ·) "" ws := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih =>
    simp
    rw [ih (acc ++ w)]
    rw [ih w]
    rw [String.append_assoc]

lemma appendAll_cons (h : String) (t : List String) : List.appendAll (h :: t) = h ++ List.appendAll t := by
  dsimp [List.appendAll]
  calc
    (h :: t).foldl (· ++ ·) default = t.foldl (· ++ ·) (default ++ h) := rfl
    _ = t.foldl (· ++ ·) h := by simp
    _ = h ++ t.foldl (· ++ ·) "" := foldl_append_acc t h
    _ = h ++ List.appendAll t := rfl

/-- `List.appendAll` distributes over snoc (appending a single element at the end).
For example, `List.appendAll (["a", "b"] ++ ["c"]) = List.appendAll ["a", "b"] ++ "c"`. -/
lemma appendAll_snoc (acc : List String) (s : String) :
    List.appendAll (acc ++ [s]) = List.appendAll acc ++ s := by
  induction acc with
  | nil =>
    simp [List.appendAll]
  | cons h t ih =>
    calc
      List.appendAll ((h :: t) ++ [s]) = List.appendAll (h :: (t ++ [s])) := by simp
      _ = h ++ List.appendAll (t ++ [s]) := by rw [appendAll_cons]
      _ = h ++ (List.appendAll t ++ s) := by rw [ih]
      _ = (h ++ List.appendAll t) ++ s := by rw [String.append_assoc]
      _ = List.appendAll (h :: t) ++ s := by rw [appendAll_cons]

/-- Folding string concatenation from the left yields character data equal to
the accumulator's data plus the flattened data of all remaining strings.
This relates the `data` view of a foldl-concatenated string to the underlying character lists. -/
lemma foldl_append_data (acc : String) (xs : List String) :
    (List.foldl (fun r s => r ++ s) acc xs).data = acc.data ++ (xs.map String.data).flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs' ih =>
    rw [List.foldl, ih, List.map, List.flatten]
    simp [List.append_assoc]

/-! ## String to character singleton strings

This section provides utilities for decomposing a `String` into a list of
single-character strings (`toCharStrings`) and the fundamental lemma that
joining singleton character strings reconstructs the original `String.mk` list.
-/

/-- Convert each character of a string into a singleton string.
`toCharStrings s` returns a `List String` where each element is a single-character
string corresponding to one character of `s`.

For example, `toCharStrings "ab" = ["a", "b"]`. -/
def toCharStrings (s : String) : List String :=
  s.toList.map (fun c => String.singleton c)

/-- Joining a list of singleton-character strings via `String.join` equals
constructing a string from the character list via `String.mk`.

This is the fundamental relationship between `String.join`, `String.singleton`,
and `String.mk`: decomposing a string into singleton characters and re-joining
them reconstructs the original character list.

For example, `String.join (List.map String.singleton ['a','b','c']) = "abc"`. -/
lemma join_map_singleton_eq_mk (l : List Char) : String.join (l.map (fun c => String.singleton c)) = String.mk l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    unfold String.join String.singleton
    simp
    rw [foldl_append_acc (List.map (fun x => "".push x) cs) ("".push c)]
    have h_ih_foldl : List.foldl (fun (r : String) (s : String) => r ++ s) "" (List.map (fun x => "".push x) cs) = String.mk cs := by
      simpa [String.join, String.singleton] using ih
    rw [h_ih_foldl]
    apply String.ext
    simp

/-! ## concatMap — map chars to strings and concatenate -/

/-- Map each character `c` of string `s` to a string via `f`, then concatenate the results.
This is the string equivalent of `List.concatMap`: `concatMap f s` replaces each character
`c` in `s` with the string `f c`.

For example, `concatMap (fun _ => "ab") "cd" = "abab"`. -/
def concatMap (f : Char → String) (s : String) : String :=
  String.join (s.data.map f)

lemma concatMap_nil (f : Char → String) : concatMap f "" = "" := by
  unfold concatMap; rfl

end String


namespace String

/-! # Split by predicate

This module provides `splitWordsAux`, a function that splits a list of characters
into maximal contiguous sequences where a given predicate holds, converting each
group to a `String`. Characters not satisfying the predicate are skipped when no
word is being accumulated.

The module also provides lemmas about the properties of the output words:
* `splitWordsAux_join` — the join of the result equals the concatenation of the
  accumulated words, the current word, and the filtered remaining characters.
* `splitWordsAux_nonempty` — all output words are nonempty.
* `splitWordsAux_alpha` — all output words consist only of characters satisfying
  the predicate.
-/

/-- Split characters into maximal contiguous sequences where the predicate holds.
`ws` accumulates completed words (in reverse order), `w` accumulates current word (reversed).
Characters not satisfying the predicate are skipped when no word is being accumulated. -/
def splitWordsAux : (Char → Bool) → List Char → List String → List Char → List String
  | p, [], ws, w =>
    let ws' := if w.isEmpty then ws else (String.mk w.reverse) :: ws
    ws'.reverse
  | p, c :: cs', ws, w =>
    if p c then
      splitWordsAux p cs' ws (c :: w)
    else
      if w.isEmpty then
        splitWordsAux p cs' ws []
      else
        splitWordsAux p cs' ((String.mk w.reverse) :: ws) []

/-- The join of splitWordsAux equals the join of ws (correctly ordered) plus
current word plus remaining filtered chars. -/
lemma splitWordsAux_join (p : Char → Bool) (cs : List Char) (ws : List String) (w : List Char) :
    String.join (splitWordsAux p cs ws w) =
    String.join ws.reverse ++ String.mk w.reverse ++ String.mk (cs.filter p) := by
  induction cs generalizing ws w with
  | nil =>
    unfold splitWordsAux
    by_cases h : w.isEmpty
    · have hw : w = [] := by simpa using h
      subst hw
      simp
    · simp [h, String.join, List.reverse_cons, String.append_assoc]
  | cons c cs' ih =>
    unfold splitWordsAux
    by_cases hc : p c
    · rw [if_pos hc]
      rw [ih ws (c :: w)]
      have h_filter : (c :: cs').filter p = c :: cs'.filter p := by
        simp [hc]
      have h_rev : (c :: w).reverse = w.reverse ++ [c] := by simp
      calc
        String.join ws.reverse ++ String.mk ((c :: w).reverse) ++ String.mk (cs'.filter p)
            = String.join ws.reverse ++ String.mk (w.reverse ++ [c]) ++ String.mk (cs'.filter p) := by
          rw [h_rev]
        _ = String.join ws.reverse ++ (String.mk w.reverse ++ String.mk [c]) ++ String.mk (cs'.filter p) := rfl
        _ = String.join ws.reverse ++ String.mk w.reverse ++ String.mk [c] ++ String.mk (cs'.filter p) := by
          simp [String.append_assoc]
        _ = String.join ws.reverse ++ String.mk w.reverse ++ (String.mk [c] ++ String.mk (cs'.filter p)) := by
          simp [String.append_assoc]
        _ = String.join ws.reverse ++ String.mk w.reverse ++ String.mk (c :: cs'.filter p) := rfl
        _ = String.join ws.reverse ++ String.mk w.reverse ++ String.mk ((c :: cs').filter p) := by
          rw [h_filter]
    · rw [if_neg hc]
      by_cases hw : w.isEmpty
      · rw [if_pos hw]
        have hw' : w = [] := by simpa using hw
        subst hw'
        rw [ih ws []]
        have h_filter : (c :: cs').filter p = cs'.filter p := by
          simp [hc]
        simp [h_filter]
      · rw [if_neg hw]
        rw [ih ((String.mk w.reverse) :: ws) []]
        have h_filter : (c :: cs').filter p = cs'.filter p := by
          simp [hc]
        simp [h_filter, String.join, List.reverse_cons, String.append_assoc]

/-- All words produced by splitWordsAux are nonempty. -/
lemma splitWordsAux_nonempty (p : Char → Bool) (cs : List Char) (ws : List String) (w : List Char)
    (hws : ∀ s ∈ ws, s ≠ "") : ∀ s ∈ splitWordsAux p cs ws w, s ≠ "" := by
  revert hws
  induction cs generalizing ws w with
  | nil =>
    intro hws
    unfold splitWordsAux
    by_cases hw : w.isEmpty
    · simp [hw]
      intro s hs
      apply hws
      simpa using hs
    · rw [if_neg hw]
      simp
      intro s hs
      rcases hs with (hs | hs)
      · apply hws
        simpa using hs
      · rw [hs]
        apply string_mk_ne_empty_of_ne_nil
        intro hrevnil
        have hnil : w = [] := List.reverse_eq_nil_iff.mp hrevnil
        simpa [hnil] using hw
  | cons c cs' ih =>
    intro hws
    unfold splitWordsAux
    by_cases hc : p c
    · rw [if_pos hc]
      exact ih ws (c :: w) hws
    · rw [if_neg hc]
      by_cases hw : w.isEmpty
      · rw [if_pos hw]
        exact ih ws [] hws
      · rw [if_neg hw]
        have hword : String.mk w.reverse ≠ "" := by
          apply string_mk_ne_empty_of_ne_nil
          intro hrevnil
          have hnil : w = [] := List.reverse_eq_nil_iff.mp hrevnil
          simpa [hnil] using hw
        apply ih ((String.mk w.reverse) :: ws) []
        intro s hs
        simp at hs
        rcases hs with (heq | hs')
        · rw [heq]
          exact hword
        · exact hws s hs'

/-- All words produced by splitWordsAux consist only of characters satisfying the predicate. -/
lemma splitWordsAux_alpha (p : Char → Bool) (cs : List Char) (ws : List String) (w : List Char)
    (hws : ∀ s ∈ ws, s.all (fun c => p c) = true)
    (hw : w.all p = true) :
    ∀ s ∈ splitWordsAux p cs ws w, s.all (fun c => p c) = true := by
  have hw_char : ∀ c ∈ w, p c = true := (List.all_eq_true.mp hw)
  revert hws hw hw_char
  induction cs generalizing ws w with
  | nil =>
    intro hws hw hw_char
    unfold splitWordsAux
    by_cases hw_empty : w.isEmpty
    · simp [hw_empty]
      intro s hs
      apply hws; simpa using hs
    · rw [if_neg hw_empty]
      simp
      intro s hs
      rcases hs with (hs | hs)
      · apply hws; simpa using hs
      · rw [hs]
        rw [String.all_iff]
        intro c hc
        rw [List.mem_reverse] at hc
        exact hw_char c hc
  | cons c cs' ih =>
    intro hws hw hw_char
    unfold splitWordsAux
    by_cases hc : p c
    · rw [if_pos hc]
      have hw' : (c :: w).all p = true := by
        simp [List.all_cons, hc, hw]
      have hw_char' : ∀ c' ∈ (c :: w), p c' = true :=
        (List.all_eq_true.mp hw')
      exact ih ws (c :: w) hws hw' hw_char'
    · rw [if_neg hc]
      by_cases hw_empty : w.isEmpty
      · rw [if_pos hw_empty]
        have hw' : ([] : List Char).all p = true := by simp
        have hw_char' : ∀ c ∈ ([] : List Char), p c = true := by
          intro c; simp
        exact ih ws [] hws hw' hw_char'
      · rw [if_neg hw_empty]
        have hword_alpha : (String.mk w.reverse).all (fun c => p c) = true := by
          rw [String.all_iff]
          intro c hc
          rw [List.mem_reverse] at hc
          exact hw_char c hc
        apply ih ((String.mk w.reverse) :: ws) []
        · intro s hs
          simp at hs
          rcases hs with (heq | hs')
          · rw [heq]; exact hword_alpha
          · exact hws s hs'
        · simp
        · intro c hc
          simp at hc

/-! ### `split` is never empty -/

/-- Core lemma: `String.splitAux` always returns a non-empty list,
regardless of the accumulator `r`. -/
lemma splitAux_ne_nil (s : String) (p : Char → Bool) (b i : String.Pos) (r : List String) :
    String.splitAux s p b i r ≠ [] := by
  unfold String.splitAux
  by_cases h : s.atEnd i
  · simp [h]
  · by_cases hp : p (s.get i)
    · simp [h, hp]
      apply splitAux_ne_nil s p (s.next i) (s.next i) (s.extract b i :: r)
    · simp [h, hp]
      apply splitAux_ne_nil s p b (s.next i) r
termination_by s.endPos.1 - i.1
decreasing_by
  · exact Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h))
      (String.lt_next s i)
  · exact Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h))
      (String.lt_next s i)

/-- `String.split p s` never returns an empty list.
Even for an empty string, `"".split p = [""]`. -/
lemma split_ne_nil (s : String) (p : Char → Bool) : s.split p ≠ [] := by
  rw [String.split_of_valid]
  have h_ne_nil := List.splitOnP_ne_nil p s.data
  intro h
  have h' : s.data.splitOnP p = [] := List.map_eq_nil_iff.mp h
  exact h_ne_nil h'

/-! ### `split` equals `[w]` when no character satisfies the predicate -/

/-- If no character in `w` satisfies `p`, then `w.split p = [w]`.
This uses `List.splitOnP_eq_single` from mathlib. -/
lemma split_eq_singleton_of_forall_not (w : String) (p : Char → Bool) (h : ∀ c ∈ w.data, ¬ p c) :
    w.split p = [w] := by
  rw [String.split_of_valid]
  have h_split := List.splitOnP_eq_single p w.data h
  simp [h_split]

/-! ### `split` of `joinWithSpaces` recovers the original list -/

/-- Splitting the result of `joinWithSpaces ws` on spaces recovers `ws`,
provided `ws` is nonempty and no word in `ws` contains a space. -/
lemma split_joinWithSpaces {ws : List String} (hne : ws ≠ [])
    (h : ∀ w ∈ ws, ∀ c ∈ w.data, c ≠ ' ') : (joinWithSpaces ws).split (· = ' ') = ws := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] =>
    have hw : ∀ c ∈ w.data, ¬ (decide (c = ' ')) := by
      intro c hc
      simpa using h w (by simp) c hc
    simp [joinWithSpaces]
    exact split_eq_singleton_of_forall_not w (fun c => decide (c = ' ')) hw
  | w :: w' :: ws' =>
    have hw : ∀ c ∈ w.data, c ≠ ' ' := h w (by simp)
    have hws : ∀ w'' ∈ (w' :: ws'), ∀ c ∈ w''.data, c ≠ ' ' := by
      intro w'' hw''
      exact h w'' (by simp [hw''])
    have hne' : (w' :: ws') ≠ [] := List.cons_ne_nil _ _
    have ih := split_joinWithSpaces hne' hws
    simp [joinWithSpaces]
    rw [String.split_of_valid]
    have hdata : (w ++ " " ++ joinWithSpaces (w' :: ws')).data =
        w.data ++ (' ' :: (joinWithSpaces (w' :: ws')).data) := by simp
    rw [hdata]
    have h_first : List.splitOnP (· = ' ')
        (w.data ++ ' ' :: (joinWithSpaces (w' :: ws')).data) =
        w.data :: List.splitOnP (· = ' ') (joinWithSpaces (w' :: ws')).data :=
      List.splitOnP_first (· = ' ') w.data (by
        intro c hc
        simpa using hw c hc
      ) ' ' (by simp) (joinWithSpaces (w' :: ws')).data
    rw [h_first]
    simp
    rw [← String.split_of_valid, ih]

/-! ### `tokenize` — convenient entry point

`tokenize p cs` splits a list of characters into substrings by grouping
consecutive characters that satisfy `p`. Characters not satisfying `p` act as
separators and are discarded. This is a convenience wrapper around
`splitWordsAux` with empty initial accumulators.

For example:
* `tokenize Char.isDigit ['1','2','a','3'] = ["12", "3"]`
* `tokenize Char.isAlpha ['h','e','l','l','o',' ','w','o','r','l','d'] = ["hello", "world"]`
-/
def tokenize (p : Char → Bool) (cs : List Char) : List String :=
  splitWordsAux p cs [] []

/-! # Split on character

Character-based string splitting utilities and theorems about the
relationship between splitting by character and `String.intercalate`.
-/

/-- Splits a string on the given character, returning the list of substrings.
This is `String.split` specialized to a single-character equality predicate. -/
def splitOnChar (s : String) (c : Char) : List String :=
  s.split (fun x => x = c)

/-- Splits a string on space characters. Convenience wrapper around `splitOnChar`. -/
def splitOnSpace (s : String) : List String :=
  splitOnChar s ' '

/-- Intercalating with the singleton of `sep` after splitting on `sep` recovers
the original string. This is the string analog of `List.intercalate_splitOn`. -/
theorem intercalate_split_id (sep : Char) (s : String) :
    String.intercalate (String.singleton sep) (splitOnChar s sep) = s := by
  unfold splitOnChar
  apply String.ext
  rw [data_intercalate, String.split_of_valid]
  have h_sep_data : (String.singleton sep).data = [sep] := rfl
  rw [h_sep_data, List.map_map]
  have h_compose : String.data ∘ String.mk = id := by
    ext cs; simp
  rw [h_compose, List.map_id]
  have h_split : s.data.splitOnP (fun x => x = sep) = s.data.splitOn sep := by
    simp [List.splitOn]
    refine congrArg (fun (f : Char → Bool) => s.data.splitOnP f) ?_
    exact funext (λ x => by
      by_cases h : x = sep
      · simp [h]
      · simp [h])
  rw [h_split]
  simpa using List.intercalate_splitOn (x := sep) (xs := s.data)

/-- Splitting on `sep`, applying a pointwise-length-preserving `f`, then intercalating `sep`
yields a string of the same length as the original. -/
lemma intercalate_split_map_length_preserved (sep : Char) (s : String) (f : String → String)
    (h : ∀ t, (f t).length = t.length) :
    (String.intercalate (String.singleton sep) ((splitOnChar s sep).map f)).length
    = s.length := by
  have aux (l : List String) :
      (String.intercalate (String.singleton sep) (l.map f)).length =
        (String.intercalate (String.singleton sep) l).length := by
    cases l with
    | nil => rfl
    | cons x xs =>
      rw [length_intercalate_nonempty _ _ (by simp), length_intercalate_nonempty _ _ (by simp)]
      simp [List.map_map, Function.comp_def, h]
  rw [aux, intercalate_split_id]

/-! ### Words from `splitOnChar` do not contain the separator -/

/-- If a word comes from splitting a string on character `c` (via `splitOnChar`),
then `c` does not appear in the word's character data. This is a fundamental
property of `splitOnChar`: the separator character is never contained in any
of the resulting substrings. -/
lemma not_mem_data_of_mem_splitOnChar {text : String} {c : Char} {s : String}
    (h : s ∈ splitOnChar text c) : c ∉ s.data := by
  unfold splitOnChar at h
  rw [String.split_of_valid] at h
  rcases List.mem_map.mp h with ⟨l, hl, rfl⟩
  have h_no : ∀ x ∈ l, decide (x = c) = false :=
    List.splitOnP_mem_not_p (fun (x' : Char) => decide (x' = c)) text.data l hl
  intro hmem
  have hcontr := h_no c hmem
  simp at hcontr

/-! ### General split result properties -/

/-- Every word from `s.split p` contains no characters satisfying `p`.
This generalizes `not_mem_data_of_mem_splitOnChar` to arbitrary predicates
(rather than just equality to a specific character). -/
lemma split_result_free (s : String) (p : Char → Bool) (w : String)
    (hw : w ∈ s.split p) (c : Char) (hc : c ∈ w.data) : p c = false := by
  rw [String.split_of_valid] at hw
  rcases List.mem_map.mp hw with ⟨l, hl, rfl⟩
  have h := List.splitOnP_mem_not_p p s.data l hl c hc
  exact h

/-! ### Split respects concatenation with a separating character -/

/-- Split respects concatenation with a separating character when the first part
is free of that character. If `a` contains no `sep`, then splitting `(a ++ [sep] ++ b)`
on `(· = sep)` gives `a` followed by the split of `b`. -/
lemma split_append_char (a b : String) (sep : Char) (ha : ∀ c ∈ a.data, c ≠ sep) :
    (a ++ String.mk [sep] ++ b).split (fun c => c = sep) =
    a :: b.split (fun c => c = sep) := by
  rw [String.split_of_valid, String.split_of_valid]
  have hdata : (a ++ String.mk [sep] ++ b).data = a.data ++ [sep] ++ b.data := by simp
  rw [hdata]
  have hsplit_aux : ∀ (pref : List Char) (suff : List Char)
      (_ : ∀ c ∈ pref, c ≠ sep),
      List.splitOnP (fun c => decide (c = sep)) (pref ++ [sep] ++ suff) =
      pref :: List.splitOnP (fun c => decide (c = sep)) suff := by
    intro pref suff hpref
    induction pref with
    | nil =>
      simp [List.splitOnP_cons, List.splitOnP_nil]
    | cons c cs ih =>
      have hc : c ≠ sep := hpref c (by simp)
      have hcs : ∀ x ∈ cs, x ≠ sep := by
        intro x hx; exact hpref x (by simp [hx])
      have h_decide : decide (c = sep) = false := by simp [hc]
      rw [show (c :: cs) ++ [sep] ++ suff = c :: (cs ++ [sep] ++ suff) by simp]
      rw [List.splitOnP_cons, h_decide]
      rw [ih hcs]
      simp [List.modifyHead]
  have hsplit := hsplit_aux a.data b.data ha
  rw [hsplit]
  simp

/-! ### Split-intercalate inverse for a single-character separator -/

/-- Split-intercalate inverse for a single-character separator.
For a non-empty list where all elements are free of `sep`,
`split (· = sep)` of `intercalate (String.mk [sep])` gives back the list. -/
lemma split_intercalate_char_inverse (l : List String) (sep : Char) (h_ne : l ≠ [])
    (h_sf : ∀ w ∈ l, ∀ c ∈ w.data, c ≠ sep) :
    (String.intercalate (String.mk [sep]) l).split (fun c => c = sep) = l := by
  induction l with
  | nil => exact (h_ne rfl).elim
  | cons a as ih =>
    cases as with
    | nil =>
      have ha : ∀ c ∈ a.data, c ≠ sep := h_sf a (by simp)
      have ha_split : a.split (fun c => c = sep) = [a] :=
        split_eq_singleton_of_forall_not a (fun c => c = sep)
          (fun c hc => by simpa using ha c hc)
      simp [String.intercalate, String.intercalate.go, ha_split]
    | cons b bs =>
      have ha : ∀ c ∈ a.data, c ≠ sep := h_sf a (by simp)
      have h_rest_sf : ∀ w ∈ b :: bs, ∀ c ∈ w.data, c ≠ sep := by
        intro w hw; exact h_sf w (by simp [hw])
      have h_rest_ne : b :: bs ≠ [] := by simp
      have ih_res := ih h_rest_ne h_rest_sf
      calc
        (String.intercalate (String.mk [sep]) (a :: b :: bs)).split (fun c => c = sep) =
            (String.intercalate.go a (String.mk [sep]) (b :: bs)).split (fun c => c = sep) := rfl
        _ = ((a ++ (String.mk [sep]) ++ String.intercalate (String.mk [sep]) (b :: bs))).split (fun c => c = sep) := by
          rw [intercalate_go_cons_expand a b (String.mk [sep]) bs]
        _ = a :: (String.intercalate (String.mk [sep]) (b :: bs)).split (fun c => c = sep) := by
          rw [split_append_char a (String.intercalate (String.mk [sep]) (b :: bs)) sep ha]
        _ = a :: (b :: bs) := by rw [ih_res]

/-! ### Length of split is preserved -/

/-- Length of a string equals the sum of split chunk lengths plus (chunk count - 1).
This relates the length of a string to the lengths of its split components. -/
lemma length_split_preserved (s : String) (p : Char → Bool) :
    s.length = ((s.split p).map String.length).sum +
    ((s.split p).length - 1) := by
  rw [String.split_of_valid]
  have h_map : (List.map String.mk (List.splitOnP p s.data)).map String.length =
      (List.splitOnP p s.data).map List.length := by simp
  rw [h_map]
  simp
  have h_slen : s.length = s.data.length := rfl
  rw [h_slen]
  have hsum := List.sum_length_splitOnP_add_countP p s.data
  have hcount := List.splitOnP_length_eq_countP_add_one p s.data
  rw [hsum]
  have h_count_eq : List.countP p s.data =
      (List.splitOnP p s.data).length - 1 := by
    omega
  rw [h_count_eq]

/-! ### `splitValidate` — validate split length and per-part predicate

`splitValidate s d n p` returns `true` iff `s` splits by delimiter `d` into exactly
`n` parts, and every part satisfies the predicate `p`. This is a convenient boolean
combinator that bundles the length check and the `all` check into one operation.

For example:
* `splitValidate "a.b.c" '.' 3 (· ≠ "") = true`
* `splitValidate "a..c" '.' 3 (· ≠ "") = false` (empty middle part)
* `splitValidate "a.b" '.' 3 (· ≠ "") = false` (wrong count) -/
def splitValidate (s : String) (d : Char) (n : Nat) (p : String → Bool) : Bool :=
  let parts := s.split (· = d)
  decide (parts.length = n) && parts.all p

/-- If `splitValidate s d n p` returns `true`, then every word in `s.split (· = d)`
satisfies `p`. This captures the "all parts satisfy `p`" component of the validation. -/
lemma splitValidate_imp_all_elem (s : String) (d : Char) (n : Nat) (p : String → Bool)
    (h : splitValidate s d n p = true) (w : String) (hw : w ∈ s.split (· = d)) : p w := by
  dsimp [splitValidate] at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hlength, hall⟩
  have hall' := (List.all_eq_true (l := s.split (· = d)) (p := p)).mp hall
  exact hall' w hw

/-- If `splitValidate s d n p` returns `true`, then `s.split (· = d)` has length `n`.
This captures the "exactly `n` parts" component of the validation. -/
lemma splitValidate_imp_length_eq (s : String) (d : Char) (n : Nat) (p : String → Bool)
    (h : splitValidate s d n p = true) : (s.split (· = d)).length = n := by
  dsimp [splitValidate] at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hlength, hall⟩
  exact of_decide_eq_true hlength

/-! ### `componentAfterSep` — validate a two-part split

`componentAfterSep sep p s` splits `s` at character `sep`. If exactly two parts result,
the predicate `p` is applied to the second component; otherwise returns `false`.

This is a specialized two-part variant of `splitValidate`, useful for patterns like
`prefix@domain` or `key:value` where only the second part needs validation.

For example:
* `componentAfterSep '@' (· ∈ ["example.com"]) "user@example.com" = true`
* `componentAfterSep '@' (· ∈ ["example.com"]) "user@other.com" = false`
* `componentAfterSep '@' (fun _ => true) "noatsign" = false`
* `componentAfterSep '@' (fun _ => true) "a@b@c" = false` (more than two parts) -/
def componentAfterSep (sep : Char) (p : String → Bool) (s : String) : Bool :=
  let parts := s.split (fun c => c = sep)
  match parts with
  | [_, component] => p component
  | _ => false

/-! ### `splitAndParse` — split on a character and parse each part

Splits the string on `sep`, then applies `f` to each segment, keeping only those
that successfully parse (via `filterMap`). Returns `[]` for the empty input.
This is useful for parsing comma-separated (or similarly delimited) values. -/

/-- Split a string on a separator character and parse each piece with `f`.
Pieces that fail to parse (i.e., `f` returns `none`) are dropped via `filterMap`.
Returns `[]` for the empty string.

For example: `splitAndParse ',' String.toNat? "1,2,3" = [1, 2, 3]`. -/
def splitAndParse (sep : Char) (f : String → Option α) (s : String) : List α :=
  if s = "" then []
  else (String.split s (fun c => c = sep)).filterMap f


lemma splitAndParse_empty (sep : Char) (f : String → Option α) : splitAndParse sep f "" = [] := rfl

/-! ### `splitOn` (separator-string based) is never empty -/

/-- Core lemma: `String.splitOnAux` (the internal helper for `splitOn`) always returns a
non-empty list when called with the standard initial arguments `0 0 0 []`. -/
lemma splitOnAux_ne_nil (s sep : String) :
    String.splitOnAux s sep 0 0 0 [] ≠ [] := by
  refine (String.splitOnAux.induct s sep
    (motive := fun b i j r => String.splitOnAux s sep b i j r ≠ [])
    ?case1 ?case2 ?case3 ?case4 0 0 0 [])
  · intro b i j r h_end
    unfold String.splitOnAux
    simp [h_end]
  · intro b i j r h_notend h_eq i_1 j_1 h_atend ih
    unfold String.splitOnAux
    have h_atend' : sep.atEnd (sep.next j) = true := by simpa using h_atend
    simpa [h_notend, h_eq, h_atend'] using ih
  · intro b i j r h_notend h_eq i_1 j_1 h_notatend ih
    unfold String.splitOnAux
    have h_notatend' : ¬ sep.atEnd (sep.next j) = true := by simpa using h_notatend
    simpa [h_notend, h_eq, h_notatend'] using ih
  · intro b i j r h_notend h_neq ih
    unfold String.splitOnAux
    simpa [h_notend, h_neq] using ih

/-- `String.splitOn s sep` never returns an empty list.
Even for an empty string, `"".splitOn " " = [""]`.
This is the separator-string analog of `String.split_ne_nil` (which uses a character predicate).
Together, these show that both `split` and `splitOn` always produce at least one element. -/
lemma splitOn_ne_nil (s sep : String) : s.splitOn sep ≠ [] := by
  unfold String.splitOn
  split
  · simp
  · exact splitOnAux_ne_nil s sep

/-- If `splitOn` returns the singleton `[s]`, then the head of the result is `some s`.
This captures the common pattern where the separator does not occur in the string:
`s.splitOn sep = [s]`, and extracting the head recovers the original string. -/
lemma splitOn_head?_eq_some_of_singleton (s sep : String) (h : s.splitOn sep = [s]) :
    (s.splitOn sep).head? = some s := by
  simp [h]

/-- Returns the first segment from `s.splitOn sep`, or `""` if the split is empty
(which never happens — `splitOn_ne_nil` guarantees non-emptiness, so this always
returns the actual head).

For example:
* `"a.b.c".splitOnHead "." = "a"`
* `"hello world".splitOnHead " " = "hello"`

Equivalently, `splitOnHead s sep = (s.splitOn sep).headD ""`. -/
def splitOnHead (s sep : String) : String :=
  match s.splitOn sep with
  | [] => ""
  | h :: _ => h

/-- `splitOnHead s sep` is always a member of `s.splitOn sep`.
This follows from `splitOn_ne_nil` and case analysis on the split result. -/
lemma splitOnHead_mem (s sep : String) : splitOnHead s sep ∈ s.splitOn sep := by
  dsimp [splitOnHead]
  have h := splitOn_ne_nil s sep
  cases hs : s.splitOn sep with
  | nil => exact absurd hs h
  | cons x xs => simp [hs]

/-! ### `splitOnNth` — n-th token after splitting

`splitOnNth s sep n` extracts the n-th token (0-indexed) after splitting `s` by
separator `sep`. Returns `""` if `n` is out of bounds.

This generalizes `splitOnHead` (which is equivalent to `splitOnNth s sep 0`).
For example:
* `splitOnNth "a,b,c" "," 1 = "b"`
* `splitOnNth "hello world" " " 0 = "hello"`
* `splitOnNth "a,b,c" "," 5 = ""` (index out of bounds) -/

def splitOnNth (s sep : String) (n : Nat) : String :=
  ((s.splitOn sep)[n]?).getD ""

/-! ### `words` (split by spaces) is never empty -/

/-- Splitting a string into words (by spaces) always yields a non-empty list.
This follows from `splitOn_ne_nil` and the definition of `String.words`. -/
lemma words_ne_nil (s : String) : words s ≠ [] := by
  unfold words
  exact splitOn_ne_nil s " "

/-! ### `tokenizeBy` — String-level tokenizer

`tokenizeBy p s` splits a string into maximal contiguous substrings where each character
satisfies `p`. Characters not satisfying `p` act as delimiters and are discarded.
This is the `String`-level wrapper around `tokenize` (which operates on `List Char`).

For example:
* `tokenizeBy Char.isDigit "123abc456" = ["123", "456"]`
* `tokenizeBy Char.isAlpha "hello world" = ["hello", "world"]`
-/
def tokenizeBy (p : Char → Bool) (s : String) : List String :=
  tokenize p s.data

/-- Split a string on non-alphabetic characters, returning the list of maximal
contiguous alphabetic substrings. Non-alphabetic characters (digits, punctuation,
whitespace, etc.) act as delimiters and are discarded.
Equivalent to `tokenizeBy Char.isAlpha`.

For example:
* `splitOnNonAlpha "hello123world" = ["hello", "world"]`
* `splitOnNonAlpha "a!b@c#" = ["a", "b", "c"]`
-/
def splitOnNonAlpha (s : String) : List String :=
  tokenizeBy Char.isAlpha s

/-! ### `tokenizeWith` — tokenize with character transformation

`tokenizeWith p f s` splits a string into maximal contiguous substrings where each
character satisfies `p`, while applying the character transformation `f` to each
matching character. Characters not satisfying `p` act as delimiters and are
discarded. This generalizes `tokenizeBy` by adding character normalization
(e.g., case-folding, diacritic stripping) in a single pass.

For example:
* `tokenizeWith Char.isAlpha Char.toLower "Hello World!" = ["hello", "world"]`
* `tokenizeWith Char.isDigit id "12ab34" = ["12", "34"]`
* `tokenizeWith (· ≥ 'a') (·) "abc123def" = ["abc", "def"]`
-/
def tokenizeWith (p : Char → Bool) (f : Char → Char) (s : String) : List String :=
  let rec aux (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] =>
        let acc' := if cur.isEmpty then acc else (String.mk (List.reverse cur)) :: acc
        acc'.reverse
    | c :: cs' =>
        if p c then
          aux cs' (f c :: cur) acc
        else
          let acc' := if cur.isEmpty then acc else (String.mk (List.reverse cur)) :: acc
          aux cs' [] acc'
  aux s.data [] []

/-! ### Split count — number of pieces after split -/

/-- Count how many pieces a string splits into by a given separator string.
Equivalent to `(s.splitOn sep).length`.
For example, `splitCount " " "hello world" = 2` and `splitCount "," "a,b,c" = 3`. -/
def splitCount (sep : String) (s : String) : Nat :=
  (s.splitOn sep).length

/-- Count the number of space-separated words in a string.
Equivalent to `splitCount " " s`. For example, `wordCount "hello world" = 2`. -/
def wordCount (s : String) : Nat := splitCount " " s

/-- Count the number of (possibly overlapping) occurrences of `substr` in `text`
by splitting `text` on `substr` and subtracting one. Since `splitOn` never returns
an empty list (`splitOn_ne_nil`), the result is always a valid natural number
(truncated subtraction makes `0 - 1 = 0`).

For example:
* `countSubstring "ba" "ababa" = 2` (occurrences at positions 1 and 3)
* `countSubstring "zz" "abc" = 0`
* `countSubstring "a" "banana" = 3` -/
def countSubstring (substr text : String) : Nat :=
  (text.splitOn substr).length - 1

/-- `countSubstring substr text` is one less than `splitCount substr text`.
This is immediate from the definitions, since splitting produces one more piece
than the number of separator occurrences. -/
lemma countSubstring_eq_splitCount_sub_one (substr text : String) :
    countSubstring substr text = splitCount substr text - 1 := rfl

/-- Split a string by a character predicate, filter out empty parts, and count the
number of remaining non-empty substrings. Equivalent to `(splitFilterNotEmpty s p).length`.
For example, `countSplitNonEmpty "a,b,,c" (· == ',') = 3`. -/
def countSplitNonEmpty (s : String) (p : Char → Bool) : Nat :=
  let parts := s.split p
  (parts.filter (fun w => w ≠ "")).length

/-- Count the number of whitespace-delimited words in a string.
Splits on all whitespace characters (`Char.isWhitespace`) and filters out empty parts,
so consecutive whitespace is treated as a single separator.
Unlike `wordCount` (which splits only on the space character `" "`),
this handles tabs, newlines, and other Unicode whitespace.
For example, `countWhitespaceWords "hello\tworld" = 2` and `countWhitespaceWords "  hello  world  " = 2`. -/
def countWhitespaceWords (s : String) : Nat := countSplitNonEmpty s (·.isWhitespace)

/-! ### Quoted delimited splitting

Split a list of characters into fields separated by a delimiter, with
support for quoted fields (delimiters inside quotes are treated as literal
characters, not field separators). This is the core algorithm behind CSV
parsing and similar delimited-text formats.

For example, `splitDelimitedLineAux ',' '"' "a,b"  [] false [] = ["a", "b"]` while
`splitDelimitedLineAux ',' '"' "a,"b,c"" [] false [] = ["a", "b,c"]` (comma
inside quotes is preserved).
-/

/-- Recursively split a list of characters into fields separated by `delim`,
with fields possibly quoted by `quote`. Handles quoted delimiters and trims whitespace.

* `delim` — the field separator character (e.g. `','` for CSV)
* `quote` — the quoting character (e.g. `'"'` for CSV)
* `chars` — the remaining input characters to process
* `cur` — the current field being accumulated (reversed)
* `inQuote` — whether we are currently inside a quoted field
* `acc` — completed fields accumulated so far (reversed)

Returns the list of parsed fields in original order. -/
def splitDelimitedLineAux (delim : Char) (quote : Char) (chars : List Char) (cur : List Char) (inQuote : Bool) (acc : List String) : List String :=
  match chars with
  | [] =>
      let field := String.mk (List.reverse cur) |>.trim
      List.reverse (field :: acc)
  | c :: cs =>
      if c = quote then
        splitDelimitedLineAux delim quote cs cur (!inQuote) acc
      else if c = delim && !inQuote then
        let field := String.mk (List.reverse cur) |>.trim
        splitDelimitedLineAux delim quote cs [] false (field :: acc)
      else
        splitDelimitedLineAux delim quote cs (c :: cur) inQuote acc

/-- Convenience entry point for `splitDelimitedLineAux`: split a `String` into fields
separated by `delim`, with fields possibly quoted by `quote`. Equivalent to
`splitDelimitedLineAux delim quote s.data [] false []`.

For example:
* `splitDelimitedLine ',' '"' "a,b,c" = ["a", "b", "c"]`
* `splitDelimitedLine ',' '"' "a,\"b,c\",d" = ["a", "b,c", "d"]` -/
def splitDelimitedLine (delim : Char) (quote : Char) (s : String) : List String :=
  splitDelimitedLineAux delim quote s.data [] false []

/-! ### `splitFilterNotEmpty` — split and drop empty segments

`splitFilterNotEmpty s p` splits `s` wherever `p` holds on a character, then filters
out empty substrings from the result. This generalizes `String.split` for tokenization
tasks where empty segments (e.g., from consecutive delimiters) are undesirable.

For example:
* `splitFilterNotEmpty "a,b,,c" (· == ',') = ["a", "b", "c"]`
* `splitFilterNotEmpty "  hello  world  " Char.isSpace = ["hello", "world"]`
-/
def splitFilterNotEmpty (s : String) (p : Char → Bool) : List String :=
  (s.split p).filter (fun w => w ≠ "")

/-- If a word `w` is in `splitFilterNotEmpty s p`, then `w ≠ ""`. -/

lemma mem_splitFilterNotEmpty_ne_empty (s : String) (p : Char → Bool) (w : String)
    (hw : w ∈ splitFilterNotEmpty s p) : w ≠ "" := by
  have h := List.of_mem_filter hw
  simpa using h

/-! ### `splitOnFilterNotEmpty` — split on a delimiter string, drop empty segments

`splitOnFilterNotEmpty s sep` splits `s` on the separator string `sep` using `splitOn`,
then filters out empty substrings from the result. This is the string-separator analog of
`splitFilterNotEmpty` (which operates on a character predicate).

For example:
* `splitOnFilterNotEmpty "a,b,,c" "," = ["a", "b", "c"]`
* `splitOnFilterNotEmpty "hello  world" " " = ["hello", "world"]`
-/

/-- Split `s` on the separator string `sep` and filter out empty substrings.
The separator defaults to `" "` for space-delimited tokenization.
For example, `splitOnFilterNotEmpty "  hello  world  " = ["hello", "world"]`. -/
def splitOnFilterNotEmpty (s : String) (sep : String := " ") : List String :=
  (s.splitOn sep).filter (fun w => w ≠ "")

/-- If a word `w` is in `splitOnFilterNotEmpty s sep`, then `w ≠ ""`. -/

lemma mem_splitOnFilterNotEmpty_ne_empty (s sep : String) (w : String)
    (hw : w ∈ splitOnFilterNotEmpty s sep) : w ≠ "" := by
  have h := List.of_mem_filter hw
  simpa using h

/-! ### `splitOnToFinset` — split on a delimiter string, collect into a `Finset`

`splitOnToFinset delim s` splits `s` by the delimiter string `delim` using `splitOn`,
then collects the parts into a `Finset String`. This is a convenient way to get a
deduplicated set of substrings from a delimited string.

For example:
* `splitOnToFinset "," "a,b,c,a" = {"a", "b", "c"}`
* `splitOnToFinset " " "hello world hello" = {"hello", "world"}`

Unlike `splitFilterNotEmpty`, this operates on a delimiter **string** (not a character
predicate) and returns a `Finset` (deduplicated, order-irrelevant) rather than a `List`.
-/

/-- Split `s` by delimiter string `delim` using `splitOn`, returning the parts as a `Finset`.
Uses `List.toFinset` to stay computable without relying on potentially-unsafe `Repr` instances. -/
def splitOnToFinset (delim : String) (s : String) : Finset String :=
  (s.splitOn delim).toFinset

/-- Extract space-separated words from a string into a `Finset`.
This is `splitOnToFinset " " s`. Deduplicates: repeated words appear only once.
For example, `wordsToFinset "hello world hello" = {"hello", "world"}`. -/
def wordsToFinset (s : String) : Finset String :=
  splitOnToFinset " " s

/-! ### `splitOnSpaceToLower` — split on spaces and lowercase each token

This is a common NLP preprocessing step: tokenize a string into words by splitting
on space characters, then convert each word to lowercase for case-insensitive matching.

For example:
* `splitOnSpaceToLower "Hello World" = ["hello", "world"]`
* `splitOnSpaceToLower "  HeLLo  WoRLD  " = ["", "", "hello", "", "world", ""]`

Note: consecutive spaces produce empty string tokens. Use `splitFilterNotEmpty`
or `splitOnFilterNotEmpty` if you need empty tokens removed. -/

/-- Split a string on space characters and convert each token to lowercase via
`String.toLower`. Equivalent to `(splitOnSpace s).map String.toLower`. -/
def splitOnSpaceToLower (s : String) : List String :=
  (splitOnSpace s).map String.toLower

/-- Tokenize a string into alphanumeric words using `tokenizeBy Char.isAlphaNum`,
then lowercase each word via `String.toLower`. Non-alphanumeric characters
(punctuation, whitespace, etc.) act as delimiters and are discarded.

For example:
* `wordsToLower "Hello, World! 123" = ["hello", "world", "123"]`
* `wordsToLower "A man, a plan, a canal: Panama!" = ["a", "man", "a", "plan", "a", "canal", "panama"]`

Contrast with `splitOnSpaceToLower` which splits only on space characters and
preserves empty-string tokens from consecutive spaces. -/
def wordsToLower (s : String) : List String :=
  (tokenizeBy Char.isAlphaNum s).map String.toLower

/-! ### `countTokenMatches` — count dictionary matches in tokenized text

Count how many space-separated, lowercased tokens from `s` appear in `dict`.
This is useful for dictionary-based word counting tasks such as sentiment analysis,
keyword scanning, and vocabulary overlap measurement.

For example:
* `countTokenMatches ["hello", "world"] "Hello World!" = 2`
* `countTokenMatches ["good"] "This is bad" = 0` -/

/-- Count how many space-separated, lowercased tokens from `s` appear in `dict`.
Tokens are extracted via `splitOnSpaceToLower`. -/
def countTokenMatches (dict : List String) (s : String) : Nat :=
  (splitOnSpaceToLower s).countP (fun w => w ∈ dict)

/-! ### `splitMatrix` — split into a matrix of tokens

`splitMatrix s lineSep fieldSep` splits `s` first by `lineSep` (dropping empty lines),
then within each line splits by `fieldSep` (dropping empty fields). This is a common
text-parsing pattern: first split into lines, then split each line into words/fields.

Default line separator is `\n`, default field separator is space.
For example:
* `splitMatrix "a b\nc d\n" = [["a","b"],["c","d"]]`
* `splitMatrix "a,b\nc,d" (· = '\n') (· = ',') = [["a","b"],["c","d"]]`
* `splitMatrix "\n\nhello world\n\n" = [["hello","world"]]` (empty lines dropped)
-/
def splitMatrix (s : String) (lineSep : Char → Bool := (· = '\n')) (fieldSep : Char → Bool := (· = ' ')) :
    List (List String) :=
  (splitFilterNotEmpty s lineSep).map (fun line => splitFilterNotEmpty line fieldSep)

/-! ### `allTokensSatisfy` — token-based validator

`allTokensSatisfy sep count pred s` splits `s` on the separator character `sep`,
checks that exactly `count` tokens are produced, and that every token satisfies `pred`.
This is a general-purpose token-based validator for formats like IPv4, IPv6, MAC addresses, etc.

For example:
* `allTokensSatisfy '.' 4 isNatInRangeB "192.168.1.1" = true`
* `allTokensSatisfy '.' 4 isNatInRangeB "invalid" = false` (wrong token count)
* `allTokensSatisfy ':' 8 (fun s => s.length = 2) "AB:CD:EF:01:23:45:67:89" = true` -/

/-- Split a string by separator `sep`, then check that there are exactly `count` tokens
and that each token satisfies predicate `pred`.
This is a general-purpose token-based validator (e.g. for IPv4, IPv6, MAC addresses). -/
def allTokensSatisfy (sep : Char) (count : Nat) (pred : String → Bool) (s : String) : Bool :=
  let parts := s.split (· = sep)
  decide (parts.length = count) && parts.all pred

/-! ### `split` data equals `splitOnP` of data -/

/-- The data of `String.split` equals `List.splitOnP` of the data.
This bridges the `String.split` API with the `List.splitOnP` API,
allowing list-level split reasoning to be lifted to strings. -/
lemma split_data_eq (s : String) (p : Char → Bool) :
    (s.split p).map String.data = List.splitOnP p s.data := by
  rw [String.split_of_valid s p]
  have h : (String.data ∘ String.mk) = (id : List Char → List Char) := by
    ext l; simp
  simp [h]

/-! ### `lastSegment` — last segment after splitting by a character

`lastSegment s sep` splits `s` on character `sep` and returns the last segment.
If `sep` does not appear in `s`, returns the whole string `s`.

For example:
* `lastSegment "file.txt" '.' = "txt"`
* `lastSegment "no-sep" '.' = "no-sep"`
* `lastSegment "a.b.c" '.' = "c"`
This is the Char-based analog of `String.afterLast` (which operates on a string separator).
-/
def lastSegment (s : String) (sep : Char) : String :=
  match (s.split (· = sep)).getLast? with
  | some seg => seg
  | none => s


lemma lastSegment_id_of_not_mem_char (s : String) (sep : Char) (h : sep ∉ s.data) :
    lastSegment s sep = s := by
  unfold lastSegment
  have hsplit : s.split (· = sep) = [s] := by
    apply String.split_eq_singleton_of_forall_not s (fun c => c = sep)
    intro c hc
    have hne : c ≠ sep := by
      intro heq; subst heq; exact h hc
    simp [hne]
  simp [hsplit]

/-! ### `splitMap` — split by predicate, then map a function over each token

`splitMap p f s` splits `s` at characters satisfying `p` (via `String.split`),
then applies `f` to each resulting token. This is a general split-and-transform
combinator that captures the common pattern of tokenizing a string and then
processing each token.

For example:
* `splitMap (· = ' ') String.toLower "Hello World" = ["hello", "world"]`
* `splitMap (· = ',') id "a,b,c" = ["a", "b", "c"]`

Contrast with `tokenizeWith` which filters AND transforms at the character level
in a single pass; `splitMap` uses the standard `String.split` API and maps
after splitting. -/
def splitMap (p : Char → Bool) (f : String → α) (s : String) : List α :=
  (s.split p).map f

end String

namespace String

/-! ## Split lines -/

/-- Split the input string into lines at every `'\n'` character. -/
def splitLines (s : String) : List String :=
  s.split (fun c => c = '\n')

/-- Split the input string into fields at every `'|'` character.
Common in CSV-like pipe-delimited formats. -/
def splitFields (s : String) : List String :=
  s.split (fun c => c = '|')

/-- Splitting the empty string by any predicate yields `[""]`.
This is the concrete value that `split_ne_nil` excludes as being the empty list. -/

lemma split_empty (p : Char → Bool) : "".split p = [""] := by
  unfold String.split
  rw [String.splitAux.eq_1 "" p 0 0 []]
  have h : "".atEnd 0 = true := by decide
  simp [h]
  decide

/-- Splitting the empty string into lines yields `[""]`. -/

lemma splitLines_empty : splitLines "" = [""] := by
  unfold splitLines
  apply split_empty

end String
