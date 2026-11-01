import Mathlib.Data.String.Basic
import fvapps.List.Basic
import fvapps.List.Count
import fvapps.List.Repeat
import Mathlib.Data.List.SplitOn
import Batteries.Data.String.Lemmas

namespace Specific

open _root_.List

namespace String

/-! ## Digit characters -/

/-- A canonical list of digit characters '0' through '9'. -/
def digitChars : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

/-- Maps a digit character to its numeric value with a configurable default for
    non-digit characters. Pattern-matches `'0'` through `'9'`, returning `0`..`9`,
    and returns `default` for any other character. -/
def Char.digitValueWithDefault (default : Nat) : Char → Nat
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
  | _ => default

/-- Returns the numeric value of a digit character.
    For `'0'` returns `0`, for `'1'` returns `1`, ..., for `'9'` returns `9`.
    For non-digit characters returns `0`. -/
def Char.digitValue (c : Char) : Nat :=
  Char.digitValueWithDefault 0 c

/-- Returns the numeric value of a digit character as an `Option Nat`.
    Returns `some 0` for `'0'`, ..., `some 9` for `'9'`, and `none` for
    non-digit characters. -/
def Char.digitValue? : Char → Option Nat
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
  | _ => none

/-- Checks if a character is a valid digit (according to `isDigit`) and is not the zero
    character (e.g., `'0'` for decimal digits). Useful for validating non-zero digit constraints
    in number parsing problems. -/
def Char.validNonzeroDigit (zero : Char) (isDigit : Char → Bool) (c : Char) : Bool :=
  isDigit c && c != zero

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

/-- Any character in the data of a `repeatChar n c` string must equal `c`. -/
theorem repeatChar_mem_data {fill c : Char} {n : Nat}
    (h : c ∈ (repeatChar n fill).data) : c = fill := by
  simp [repeatChar] at h
  exact h.2

/-- If `c ≠ sep`, splitting `repeatChar n c` on `(· = sep)` yields a singleton list
containing the original string. This is a convenient specialization of
`split_eq_singleton_of_forall_not` for repeated-character strings. -/
theorem repeatChar_split_ne {c sep : Char} (n : Nat) (h : c ≠ sep) :
    (repeatChar n c).split (· = sep) = [repeatChar n c] := by
  rw [repeatChar, String.split_of_valid]
  have hsplit :
      List.splitOnP (fun x => decide (x = sep)) (List.replicate n c) =
        [List.replicate n c] := by
    apply List.splitOnP_eq_single
    intro x hx
    rcases (List.mem_replicate.mp hx) with ⟨_, rfl⟩
    simp [h]
  simp [hsplit]

/-- Creates a string by prepending `n` copies of character `c` before `suffix`.
`replicatePrefix 'x' 3 ['y','z']` = `"xxxyz"`. -/
def replicatePrefix (c : Char) (n : Nat) (suffix : List Char) : String :=
  String.mk (List.replicate n c ++ suffix)

/-- The length of `replicatePrefix c n suffix` is at least `n`. -/
theorem length_replicatePrefix_ge (c : Char) (suffix : List Char) (n : Nat) :
    (replicatePrefix c n suffix).length ≥ n := by
  unfold replicatePrefix
  rw [String.length_mk]
  simp

/-- Creates a string with `i` copies of `fill`, then `sep`, then `j` copies of `fill`.
`separatedReplicate 'x' '/' 3 2` = `"xxx/xx"`. -/
def separatedReplicate (fill sep : Char) (i j : Nat) : String :=
  String.mk (List.separatedReplicate fill sep i j)

/-- The length of `separatedReplicate fill sep i j` is `i + 1 + j`. -/
@[simp]
theorem separatedReplicate_length (fill sep : Char) (i j : Nat) :
    (separatedReplicate fill sep i j).length = i + 1 + j := by
  simp [separatedReplicate, String.length]

/-- Constructs a uniform string from a value by extracting its length and character. -/
def uniformByLength {α : Type} (lengthOf : α → Nat) (choose : α → Char) (x : α) : String :=
  repeatChar (lengthOf x) (choose x)

@[simp]
theorem uniformByLength_length {α : Type} (lengthOf : α → Nat) (choose : α → Char) (x : α) :
    (uniformByLength lengthOf choose x).length = lengthOf x := by
  simp [uniformByLength]

/-! ## String repetition -/

/-- Repeat a string `s` `n` times by repeated concatenation.
`repeatStr n "abc"` = `"abcabc...abc"` (n times). -/
def repeatStr (n : Nat) (s : String) : String :=
  List.repeatFold (· ++ ·) "" n s

@[simp]
theorem repeatStr_length (n : Nat) (s : String) : (repeatStr n s).length = s.length * n := by
  unfold repeatStr
  simpa using
    List.repeatFold_size_of_size_empty_zero String.length (· ++ ·) "" s
      String.length_append rfl n

/-! ## Flattening lists of strings -/

/-- Flattens a list of strings into a single list of all their characters.
`flattenChars ["ab", "cd"]` = `['a', 'b', 'c', 'd']`. -/
def flattenChars (strings : List String) : List Char :=
  strings.flatMap String.toList

/-! ## Length and emptiness -/

/-- If a string has positive length, it is not the empty string. -/
theorem ne_empty_of_length_pos {s : String} (h : 0 < s.length) : s ≠ "" := by
  intro hs
  subst hs
  simp at h

/-- If the underlying character data of a string is empty, the string must be `""`. -/
theorem eq_empty_of_data_eq_nil {s : String} (h : s.data = []) : s = "" := by
  cases s with
  | mk data =>
      simp at h
      cases h
      rfl

/-! ## String predicates -/

/-- `satisfies p minLen s` holds if `s` has length at least `minLen` and every
character in `s` satisfies the boolean predicate `p`.
This combines a minimum-length constraint with `allCharsIn`. -/
def satisfies (p : Char → Bool) (minLen : Nat) (s : String) : Prop :=
  s.length ≥ minLen ∧ ∀ c, c ∈ s.data → p c

/-- A `Prop`-valued predicate: `allChars p s` holds if every character in `s` satisfies `p`.
    Equivalent to `∀ c ∈ s.data, p c`. -/
def allChars (p : Char → Prop) (s : String) : Prop :=
  ∀ c ∈ s.data, p c

/-- A `Bool`-valued predicate: `allCharsIn allowed s` returns `true` if every character
    in `s` belongs to the `allowed` list. Useful for character-set validation (e.g.,
    checking that a string contains only digit characters). -/
def allCharsIn (allowed : List Char) (s : String) : Bool :=
  s.data.all fun c => c ∈ allowed

/-- `allCharsIn allowed s` is `true` iff every character in `s` belongs to `allowed`. -/
theorem allCharsIn_eq_true (allowed : List Char) (s : String) :
    allCharsIn allowed s = true ↔ ∀ c ∈ s.data, c ∈ allowed := by
  simp [allCharsIn, List.all_eq_true]

/-- `containsChar p s` returns `true` if there exists a character in `s` satisfying `p`.
    This is the `Bool`-valued existential counterpart to `allChars` (the universal one),
    and the dual of `countStringBy p s = 0`. -/
def containsChar (p : Char → Bool) (s : String) : Bool :=
  s.data.any p

/-! ## Character range predicates -/

/-- `Char.between lo hi c` holds if `c` is inclusively between `lo` and `hi`. -/
def Char.between (lo hi c : Char) : Prop :=
  lo ≤ c ∧ c ≤ hi

/-- `allCharsBetween lo hi s` holds if every character in `s` is between `lo` and `hi`
    inclusive. Defined as `allChars (Char.between lo hi) s`. -/
def allCharsBetween (lo hi : Char) (s : String) : Prop :=
  allChars (Char.between lo hi) s

/-- Checks that `s` is non-empty and all its characters satisfy predicate `p`. -/
def nonemptyAll (p : Char → Bool) (s : String) : Bool :=
  s.length > 0 && s.data.all p

@[simp]
theorem nonemptyAll_eq_true {p : Char → Bool} {s : String}
    (hLength : s.length > 0) (hAll : s.data.all p = true) :
    nonemptyAll p s = true := by
  unfold nonemptyAll
  simp [hLength, hAll]

/-! ## Palindrome checking -/

/-- Checks whether a `String` is a palindrome (reads the same forwards and backwards).
    Wraps the general `List` palindrome check via `String.toList`. -/
def is_palindrome (s : String) : Bool :=
  decide (s.toList = s.toList.reverse)

@[simp]
theorem is_palindrome_empty : is_palindrome "" = true := by
  simp [is_palindrome]

theorem is_palindrome_iff_toList_eq_reverse (s : String) :
    is_palindrome s = true ↔ s.toList = s.toList.reverse := by
  simp [is_palindrome]

/-! ## String splitting -/

/-- Splits a string on occurrences of `separator`, returning a list of substrings.
A convenience wrapper around `String.split`. -/
def splitOnChar (separator : Char) (s : String) : List String :=
  s.split (· = separator)

/-- Returns the first field (substring before the first occurrence of `separator`)
of a string. Equivalent to `(s.splitOn separator).head` but uses `[0]!` for
direct access. Since `String.splitOn` always returns a non-empty list,
`[0]!` is safe. -/
def firstField (separator : String) (s : String) : String :=
  (s.splitOn separator)[0]!

/-- Splitting `String.mk xs` on `p` returns a singleton list `[String.mk xs]` when
no character in `xs` satisfies `p`. -/
theorem split_eq_singleton_of_forall_not {p : Char → Prop} [DecidablePred p]
    (xs : List Char) (h : ∀ c ∈ xs, ¬ p c) :
    (String.mk xs).split p = [String.mk xs] := by
  rw [String.split_of_valid]
  simp [List.splitOnP, List.splitOnP_go_eq_singleton_of_forall_not xs [] h]

/-- For a single-character separator `c`, `String.splitOn` is equivalent to
`List.splitOnP` on the character data, mapped back to strings.
This bridges the string-level `splitOn` with list-level reasoning. -/
theorem splitOn_singleton_eq_map_splitOnP (s : String) (c : Char) :
    s.splitOn (String.singleton c) =
    (List.splitOnP (fun x : Char => x == c) s.data).map String.mk := by
  have splitOnAux_singleton_of_valid (c : Char) (l m r : List Char)
      (acc : List String) :
      String.splitOnAux ⟨l ++ m ++ r⟩ (String.singleton c)
        ⟨String.utf8Len l⟩ ⟨String.utf8Len l + String.utf8Len m⟩ 0 acc =
        acc.reverse ++ (List.splitOnP.go (fun x => x == c) r m.reverse).map String.mk := by
    induction r generalizing l m acc with
    | nil =>
      rw [String.splitOnAux]
      simp [String.atEnd_iff, String.endPos_eq, String.utf8Len_append,
        List.splitOnP.go, String.extract_of_valid]
      simpa using String.extract_of_valid l m []
    | cons a r ih =>
      rw [String.splitOnAux]
      simp only [List.append_assoc, String.atEnd_iff, String.endPos_eq,
        String.utf8Len_append, String.utf8Len_cons, String.Pos.mk_le_mk]
      rw [if_neg (by have := Char.utf8Size_pos a; omega)]
      have hg : (String.mk (l ++ (m ++ a :: r))).get
          ⟨String.utf8Len l + String.utf8Len m⟩ = a := by
        simpa using String.get_of_valid (l ++ m) (a :: r)
      have hn : (String.mk (l ++ (m ++ a :: r))).next
          ⟨String.utf8Len l + String.utf8Len m⟩ =
          ⟨String.utf8Len l + String.utf8Len m + a.utf8Size⟩ := by
        simpa using String.next_of_valid (l ++ m) a r
      have hs : (String.singleton c).get 0 = c := by rfl
      have hsn : (String.singleton c).next 0 = ⟨c.utf8Size⟩ := by
        simpa using String.next_of_valid [] c []
      have hend : (String.singleton c).endPos = ⟨c.utf8Size⟩ := by
        change (String.mk [c]).endPos = _
        simp
      simp only [hg, hs, hn, hsn, List.splitOnP.go]
      by_cases h : a = c
      · subst a
        simp only [beq_self_eq_true, Bool.true_eq, ↓reduceIte,
          String.atEnd_iff, hend,
          String.utf8Len_cons, String.utf8Len_nil, Nat.zero_add,
          String.Pos.mk_le_mk, le_refl, List.map_cons, List.reverse_cons]
        have he : (String.Pos.mk (String.utf8Len l + String.utf8Len m + c.utf8Size) -
            String.Pos.mk c.utf8Size) = ⟨String.utf8Len l + String.utf8Len m⟩ := by
          apply String.Pos.ext; simp
        rw [he]
        have hex := String.extract_of_valid l m (c :: r)
        simp only [List.append_assoc] at hex
        rw [hex]
        simpa [List.append_assoc, Nat.add_assoc] using ih (l ++ m ++ [c]) [] (String.mk m :: acc)
      · simp only [beq_iff_eq, h, ↓reduceIte]
        have hz : (String.Pos.mk (String.utf8Len l + String.utf8Len m) - 0) =
            ⟨String.utf8Len l + String.utf8Len m⟩ := by
          apply String.Pos.ext; simp
        rw [hz, hn]
        simpa [List.append_assoc, Nat.add_assoc] using ih l (m ++ [a]) acc
  simpa [String.splitOn, String.singleton] using
    splitOnAux_singleton_of_valid c [] [] s.data []

/-- If no character in `s` equals `c`, splitting on `String.singleton c` returns `[s]`.
This is the `String.splitOn` analogue of `split_eq_singleton_of_forall_not`. -/
theorem splitOn_singleton_eq_singleton_of_forall_not (s : String) (c : Char)
    (h : ∀ x ∈ s.data, x ≠ c) :
    s.splitOn (String.singleton c) = [s] := by
  rw [splitOn_singleton_eq_map_splitOnP]
  have h' : ∀ x ∈ s.data, ¬(fun x' : Char => x' == c) x := by
    intro x hx hbeq
    have heq : x = c := beq_iff_eq.mp hbeq
    exact h x hx heq
  rw [List.splitOnP_eq_single (fun x' : Char => x' == c) s.data h']
  simp

/-- Joins a list of strings with a character separator.
`joinWithChar ',' ["a", "b", "c"] = "a,b,c"`. -/
def joinWithChar (sep : Char) (words : List String) : String :=
  String.mk (List.intercalate [sep] (words.map String.data))

private lemma map_string_mk_data (words : List String) :
    (words.map String.data).map String.mk = words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    simp [List.map, ih]

/-- Splitting on `sep` is a left inverse of `joinWithChar sep`, provided `sep`
does not appear in any of the words to be joined.
`splitOnChar sep (joinWithChar sep words) = words`. -/
lemma splitOnChar_joinWithChar (sep : Char) (words : List String)
    (hsep : ∀ word ∈ words, sep ∉ word.data) (hwords : words ≠ []) :
    splitOnChar sep (joinWithChar sep words) = words := by
  unfold splitOnChar joinWithChar
  rw [String.split_of_valid]
  -- The core of the proof: `List.splitOn_intercalate` from Mathlib gives the key equality
  have hsplit_intercalate :
      List.splitOn sep (List.intercalate [sep] (words.map String.data)) =
        words.map String.data := by
    apply List.splitOn_intercalate (words.map String.data) sep
    · intro l hl hmem
      rcases List.mem_map.mp hl with ⟨word, hword, rfl⟩
      exact hsep word hword hmem
    · intro hnil
      apply hwords
      simpa using (List.map_eq_nil_iff.mp hnil)
  have hsplitP :
      List.splitOnP (fun x => decide (x = sep))
          (List.intercalate [sep] (words.map String.data)) =
        words.map String.data := by
    have hsplitBEq :
        List.splitOnP (· == sep)
            (List.intercalate [sep] (words.map String.data)) =
          words.map String.data := by
      simpa [List.splitOn] using hsplit_intercalate
    have hpred_eq : (fun (x : Char) => (x == sep)) = (fun x => decide (x = sep)) := by
      funext x
      by_cases h : x = sep
      · subst h; simp
      · have hbeq : (x == sep) = false :=
          Bool.eq_false_iff.mpr (fun hb => h (eq_of_beq hb))
        simp [h, hbeq]
    simpa [hpred_eq] using hsplitBEq
  calc
    (List.splitOnP (fun x => decide (x = sep))
        (List.intercalate [sep] (words.map String.data))).map String.mk =
        (words.map String.data).map String.mk := by rw [hsplitP]
    _ = words := map_string_mk_data words

/-- Splitting a string on any character yields a non-empty list. -/
lemma splitOnChar_ne_nil (sep : Char) (s : String) : splitOnChar sep s ≠ [] := by
  unfold splitOnChar
  rw [String.split_of_valid]
  intro hnil
  exact List.splitOnP_ne_nil _ _ (List.map_eq_nil_iff.mp hnil)

/-! ## String joining -/

/-- Joins a list of strings with a string separator.
`joinWith ", " ["a", "b", "c"] = "a, b, c"`.
For a single-element list returns the element unchanged.
For the empty list returns `""`.
This is a recursive definition, easier to reason about with induction
than `String.intercalate` (which is defined via `List.intersperse`). -/
def joinWith (sep : String) : List String → String
  | [] => ""
  | [part] => part
  | part :: rest => part ++ sep ++ joinWith sep rest

/-! ## Character counting -/

/-- Count how many times `needle` appears in string `s`. -/
def countChar (needle : Char) (s : String) : Nat :=
  List.countMatches needle s.toList

/-- `countChar` is always nonnegative. -/
theorem countChar_nonneg (needle : Char) (s : String) :
    countChar needle s ≥ 0 :=
  List.countMatches_nonneg needle s.toList

/-! ## Bool-predicate character counting -/

/-- Count how many characters in `s` satisfy the Bool predicate `p`.
Defined via `List.countBy` on the string's internal character data. -/
def countStringBy (p : Char → Bool) (s : String) : Nat :=
  List.countBy p s.data

/-- `countStringBy` is always nonnegative. -/
theorem countStringBy_non_negative (p : Char → Bool) (s : String) :
    countStringBy p s ≥ 0 := by
  exact List.countBy_non_negative p s.data

/-- `countStringBy` is bounded by the string length. -/
theorem countStringBy_bounded (p : Char → Bool) (s : String) :
    countStringBy p s ≤ s.length := by
  exact List.countBy_bounded p s.data

/-- If all characters satisfy the predicate, `countStringBy` equals the string length. -/
theorem countStringBy_eq_length_of_all {p : Char → Bool} {s : String}
    (h : ∀ c ∈ s.data, p c = true) :
    countStringBy p s = s.length := by
  exact List.countBy_eq_length_of_all h

/-- If no character satisfies the predicate, `countStringBy` is zero. -/
theorem countStringBy_eq_zero_of_none {p : Char → Bool} {s : String}
    (h : ∀ c ∈ s.data, p c = false) :
    countStringBy p s = 0 := by
  exact List.countBy_eq_zero_of_none h

/-- A list of hexadecimal digit characters '0'-'9' and 'A'-'F'. -/
def hexDigitChars : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

/-! ## Character mapping -/

/-- Map a `Char → Char` function over each character of a `String`.
Returns a new string with the mapped character data. -/
def mapChars (f : Char → Char) (s : String) : String :=
  String.mk (s.data.map f)

/-- Mapping chars preserves string length. -/
@[simp]
theorem mapChars_length (f : Char → Char) (s : String) :
    (mapChars f s).length = s.length := by
  cases s
  simp [mapChars, String.length]

/-! ## Mathlib `String.map` and case-conversion length lemmas

These lemmas cover Mathlib's own `String.map`, `String.toLower`, and
`String.toUpper` — some problems use these directly instead of the
custom general `mapChars`. -/

/-- Mapping a character function over a `String` using Mathlib's `String.map`
preserves its length. -/
@[simp]
theorem map_length (f : Char → Char) (s : String) : (s.map f).length = s.length := by
  rw [String.map_eq]
  simp [String.length_data]

/-- Converting a string to lowercase preserves its length. -/
@[simp]
theorem toLower_length (s : String) : s.toLower.length = s.length := by
  simp [String.toLower, map_length]

/-- Converting a string to uppercase preserves its length. -/
@[simp]
theorem toUpper_length (s : String) : s.toUpper.length = s.length := by
  simp [String.toUpper, map_length]

/-- Reverse the character data of a string.
`reverse "abc" = "cba"`. Defined as `String.mk s.data.reverse`. -/
def reverse (s : String) : String :=
  String.mk s.data.reverse

/-- Reversing a string preserves its length. -/
@[simp]
theorem reverse_length (s : String) : (reverse s).length = s.length := by
  unfold reverse
  rw [String.length_mk, List.length_reverse, String.length]

/-- If a string has length at most 1, reversing it yields the same string. -/
theorem reverse_eq_of_length_le_one (s : String) (h : s.length ≤ 1) : reverse s = s := by
  apply String.ext
  unfold reverse
  -- `String.length` is `s.data.length`, so `h` already gives the needed bound
  exact List.reverse_eq_of_length_le_one s.data h

/-- Reverse the character data of a string and then map `f` over each character.
Equivalent to `mapChars f (reverse s)` but without needing a separate `reverse` def. -/
def reverseMap (f : Char → Char) (s : String) : String :=
  String.mk (s.data.reverse.map f)

/-- `reverseMap` preserves string length. -/
@[simp]
theorem reverseMap_length (f : Char → Char) (s : String) :
    (reverseMap f s).length = s.length := by
  unfold reverseMap
  rw [String.length_mk, List.length_map, List.length_reverse, String.length]

/-- If `c` is in the character data of `s`, then `f c` is in the character data
of `reverseMap f s`. -/
theorem mem_reverseMap_of_mem {f : Char → Char} {s : String} {c : Char}
    (h : c ∈ s.data) : f c ∈ (reverseMap f s).data := by
  change f c ∈ s.data.reverse.map f
  rw [List.mem_map]
  exact ⟨c, List.mem_reverse.mpr h, rfl⟩

/-! ## String position arithmetic -/

/-- If two characters have the same UTF-8 size, then adding either of them
to the same `String.Pos` yields the same position. -/
theorem Pos.add_char_eq_of_utf8Size_eq (i : String.Pos) {a b : Char}
    (h : a.utf8Size = b.utf8Size) : i + a = i + b := by
  cases i
  simp [HAdd.hAdd, h]

/-! ## Substring equality and comparison -/

/-- Given two strings `⟨l₁ ++ m ++ r₁⟩` and `⟨l₂ ++ m ++ r₂⟩`, the `substrEq.loop`
comparison on the subrange corresponding to `m` returns `true`. This is a key
building block for reasoning about `String.startsWith`, `String.substrEq`, and
related prefix/suffix operations.

The lemma says that if both strings have a common middle segment `m` (possibly
with different prefixes `l₁`/`l₂` and suffixes `r₁`/`r₂`), then the byte-level
comparison of the `m` segments is `true`. -/
theorem substrEqLoopPrefixAux (l₁ l₂ m r₁ r₂ : List Char) :
    String.substrEq.loop ⟨l₁ ++ m ++ r₁⟩ ⟨l₂ ++ m ++ r₂⟩
      ⟨String.utf8Len l₁⟩ ⟨String.utf8Len l₂⟩
      ⟨String.utf8Len l₁ + String.utf8Len m⟩ = true := by
  induction m generalizing l₁ l₂ with
  | nil =>
      unfold String.substrEq.loop
      simp
  | cons c cs ih =>
      unfold String.substrEq.loop
      simp only
      rw [dif_pos]
      · have hget₁ :
            (⟨l₁ ++ c :: cs ++ r₁⟩ : String).get ⟨String.utf8Len l₁⟩ = c := by
            simpa [List.append_assoc] using String.get_of_valid l₁ (c :: cs ++ r₁)
        have hget₂ :
            (⟨l₂ ++ c :: cs ++ r₂⟩ : String).get ⟨String.utf8Len l₂⟩ = c := by
            simpa [List.append_assoc] using String.get_of_valid l₂ (c :: cs ++ r₂)
        rw [hget₁, hget₂]
        simp
        simpa [String.Pos.ext_iff, String.Pos.addChar_eq, String.utf8Len_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (l₁ := l₁ ++ [c]) (l₂ := l₂ ++ [c])
      · simp [String.utf8Len_cons, Nat.add_assoc]
        exact Or.inr (Char.utf8Size_pos c)

/-! ## Trimming strings by predicate -/

/-- Trims a string by removing leading and trailing characters that satisfy predicate `p`.
`trimStringBy` generalizes `String.trim` (which trims whitespace only). -/
def trimStringBy (p : Char → Bool) (s : String) : String :=
  String.mk (List.trimList p s.data)

/-- `trimStringBy` never increases the length of the string. -/
theorem trimStringBy_length_le (p : Char → Bool) (s : String) :
    String.length (trimStringBy p s) ≤ String.length s := by
  cases s
  rename_i data
  simp [trimStringBy, String.length]
  exact List.trimList_length_le p data

end String

namespace Nat

/-- Returns the hexadecimal digit character for `n` (0 → '0', ..., 15 → 'F').
    For `n ≥ 16`, returns 'F' as a fallback. -/
def hexDigitChar (n : Nat) : Char :=
  (String.hexDigitChars[n]?).getD 'F'

end Nat

end Specific
