import Mathlib
import general.List.Slicing
import general.String.CharacterStatistics
import general.String.Validation
import general.String.Normalization

namespace String

/-! ## Basic substring extraction -/

/-- Extract a substring of `str` starting at index `i` with length `len`. -/
def substr (str : String) (i len : Nat) : String :=
  (str.drop i).take len

lemma substr_len_zero (str : String) (i : Nat) : substr str i 0 = "" := by
  first
  | (solve
    | rfl
    | simp_all [substr]
    | omega
    | aesop
    | simp_all [substr, List.foldl, List.foldr]
    | simp_all [substr, Nat.absDiff])

/-- The length of `substr s i l` is `l` when `i + l ≤ s.length`. -/
lemma substr_length (s : String) (i l : Nat) (h : i + l ≤ s.length) :
    (substr s i l).length = l := by
  rw [substr, String.take_eq, String.drop_eq]
  simp [String.mk_length, List.length_take, List.length_drop]
  omega

/-- The general length formula for `substr`. -/
lemma substr_length_eq (s : String) (i len : Nat) :
    (substr s i len).length = min len (s.length - i) := by
  rw [substr, String.take_eq, String.drop_eq]
  simp [String.mk_length, List.length_take, List.length_drop]

lemma substr_length_le (s : String) (i len : Nat) :
    (substr s i len).length ≤ len := by
  rw [substr_length_eq]
  exact Nat.min_le_left _ _

lemma substr_length_eq_of_le (s : String) (i len : Nat) (h : len ≤ s.length - i) :
    (substr s i len).length = len := by
  rw [substr_length_eq]
  exact Nat.min_eq_left h

/-! ## Character uniqueness in substrings -/

/-- Returns true if all characters in the substring of `s` of length `len` starting at `start` are distinct (no duplicates). -/
def substringAllUnique (s : String) (start len : Nat) : Bool :=
  ((s.drop start).take len).data.Nodup


theorem substringAllUnique_eq_true_iff (s : String) (start len : Nat) :
    substringAllUnique s start len = true ↔ ((s.drop start).take len).data.Nodup := by
  simp [substringAllUnique]

/-! ## Substring by index range -/

/-- Extract substring from `i` to `j` (inclusive).
Returns `(s.drop i).take (j - i + 1)`. -/
def substring (s : String) (i j : Nat) : String :=
  (s.drop i).take (j - i + 1)

/-- Building a string from `s.data` after `drop i` and `take n` equals `(s.drop i).take n`.
This bridges list-of-characters operations and string-level operations, useful when converting
between `s.data` (or `s.toList`) level reasoning and `String.drop`/`String.take` reasoning. -/
lemma mk_of_data_drop_take (s : String) (i n : Nat) :
    String.mk ((s.data.drop i).take n) = (s.drop i).take n := by
  ext; simp

/-! ## Fixed-length substrings -/

/-- All contiguous substrings of `s` of exactly length `k`. Returns an empty list if `k > s.length`.
Uses `List.range` to enumerate start indices, then extracts each substring via `(s.drop i).take k`. -/
def substringsOfLength (s : String) (k : Nat) : List String :=
  if s.length < k then
    []
  else
    (List.range (s.length - k + 1)).map (fun i => (s.drop i).take k)

/-- When the string is shorter than the requested substring length, `substringsOfLength` returns the
empty list. This matches the behavior of `slidingWindows` in the standard sliding-window pattern. -/
lemma substringsOfLength_eq_nil_of_length_lt (s : String) (k : Nat) (h : s.length < k) :
    substringsOfLength s k = [] := by
  unfold substringsOfLength
  simp [h]

/-- When `s.length ≥ k`, the length of `substringsOfLength s k` is `s.length - k + 1`.
This is the number of starting positions for a window of size `k` in a string of length `s.length`. -/
lemma substringsOfLength_length (s : String) (k : Nat) (hk : k ≤ s.length) :
    (substringsOfLength s k).length = s.length - k + 1 := by
  unfold substringsOfLength
  have h_not_lt : ¬ s.length < k := by omega
  simp [h_not_lt]

/-- Every substring returned by `substringsOfLength s k` has length exactly `k`.
This is the key correctness property: the function returns substrings of the requested
length, not shorter or longer. Follows from `substr_length` because each substring is
`(s.drop i).take k = substr s i k` with `i + k ≤ s.length`. -/
lemma length_of_mem_substringsOfLength (s : String) (k : Nat) (t : String)
    (h : t ∈ substringsOfLength s k) : t.length = k := by
  unfold substringsOfLength at h
  split at h
  · simp at h
  · simp only [List.mem_map, List.mem_range] at h
    rcases h with ⟨i, hi, rfl⟩
    have hi_bound : i + k ≤ s.length := by
      have : i < s.length - k + 1 := hi
      omega
    simpa [substr] using substr_length s i k hi_bound

/-! ## Substrings with minimum length -/

/-- All contiguous substrings of `s` whose length is at least `k`.
For each start position `i` from `0` to `s.length`, every valid length `len` from `k` to `s.length - i`
yields `substr s i len`. The result preserves the natural order: by start index, then by length.
For example, `substringsOfMinLength "abc" 2 = ["ab", "abc", "bc"]`. -/
def substringsOfMinLength (s : String) (k : Nat) : List String :=
  let n := s.length
  (List.range (n + 1)).flatMap fun i =>
    ((List.range (n - i + 1)).filter (fun len => len ≥ k)).map (fun len => substr s i len)

/-- Membership in `substringsOfMinLength s k` is equivalent to being a substring of the form
`substr s i len` with `len ≥ k` and valid bounds. -/
lemma mem_substringsOfMinLength_iff (t s : String) (k : Nat) :
    t ∈ substringsOfMinLength s k ↔
    ∃ i, i < s.length + 1 ∧ ∃ len, len < s.length - i + 1 ∧ len ≥ k ∧ t = substr s i len := by
  unfold substringsOfMinLength
  simp [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨i, hi, len, ⟨hlen, hlenk⟩, heq⟩
    exact ⟨i, hi, len, hlen, hlenk, heq.symm⟩
  · rintro ⟨i, hi, len, hlen, hlenk, heq⟩
    exact ⟨i, hi, len, ⟨hlen, hlenk⟩, heq.symm⟩

/-! ## Filtered substrings of fixed length -/

/-- All contiguous substrings of `s` of exactly length `len` that satisfy predicate `p`.
Returns an empty list if `len > s.length`. Uses `substr` for substring extraction
and `filterMap` for filtering. Generalizes `substringsOfLength` by adding a predicate filter.

For example, `filterSubstringsOfLength "abc123def" 3 Char.isDigit` returns all three-digit
numeric substrings. -/
def filterSubstringsOfLength (s : String) (len : Nat) (p : String → Bool) : List String :=
  if s.length < len then
    []
  else
    (List.range (s.length - len + 1)).filterMap (fun i =>
      let sub := s.substr i len
      if p sub then some sub else none)

/-- Characterisation lemma: a substring `sub` appears in the output of
`filterSubstringsOfLength s len p` exactly when it satisfies the predicate `p`
and occurs at some position `i` within bounds.

This generalizes the pattern of scanning a string for all fixed-length substrings
that match a criterion (e.g., phone numbers, codes, patterns). -/
lemma mem_filterSubstringsOfLength_iff (s : String) (len : Nat) (p : String → Bool) (sub : String) :
    sub ∈ filterSubstringsOfLength s len p ↔
    (p sub = true ∧ ∃ i, i + len ≤ s.length ∧ s.substr i len = sub) := by
  unfold filterSubstringsOfLength
  by_cases hlen : s.length < len
  · rw [if_pos hlen]
    constructor
    · intro h; simp at h
    · intro ⟨hp, i, hi_bound, hsub⟩
      omega
  · rw [if_neg hlen]
    constructor
    · intro h
      rw [List.mem_filterMap] at h
      rcases h with ⟨i, hi, h_eq⟩
      have hi_range : i < s.length - len + 1 := List.mem_range.mp hi
      have h_bound : i + len ≤ s.length := by
        have : i ≤ s.length - len := by omega
        omega
      -- h_eq: (fun i => let sub := ...; if p sub then some sub else none) i = some sub
      -- Simplify the lambda to extract p = true and substr = sub
      have h_eq' : (if p (s.substr i len) then some (s.substr i len) else none) = some sub := by
        simpa using h_eq
      match hp : p (s.substr i len) with
      | true =>
        simp [hp] at h_eq'
        subst h_eq'
        exact ⟨hp, i, h_bound, rfl⟩
      | false =>
        simp [hp] at h_eq'
    · intro ⟨hp, i, hi_bound, hsub⟩
      have hi_mem : i ∈ List.range (s.length - len + 1) := by
        apply List.mem_range.mpr
        have : i ≤ s.length - len := by omega
        omega
      rw [List.mem_filterMap]
      exact ⟨i, hi_mem, by simp [hsub, hp]⟩

/-- Returns true if there exists a substring of `s` of length `len` satisfying predicate `P`.
`P` is applied to the character data (`List Char`) of the substring.
This avoids materializing all substrings into a list, checking existence efficiently. -/
def hasSubstringOfLen (s : String) (P : List Char → Bool) (len : Nat) : Bool :=
  (List.range (s.length + 1)).any (λ i =>
    (i + len ≤ s.length) && P (((s.drop i).take len).data))

/-- `hasSubstringOfLen s P len` is true iff there exists an index `i` such that
`i + len ≤ s.length` and the substring of length `len` starting at `i` satisfies `P`.
This lemma bridges the boolean function to the existential statement used in proofs. -/
lemma hasSubstringOfLen_iff (s : String) (P : List Char → Bool) (len : Nat) :
    hasSubstringOfLen s P len ↔
    ∃ i, i + len ≤ s.length ∧ P (((s.drop i).take len).data) := by
  dsimp [hasSubstringOfLen]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi_mem, hcond⟩
    have hi_lt : i < s.length + 1 := by
      simpa [List.mem_range] using hi_mem
    rw [Bool.and_eq_true] at hcond
    rcases hcond with ⟨h_bound_true, hP_true⟩
    have h_bound : i + len ≤ s.length := by
      simpa using h_bound_true
    exact ⟨i, h_bound, hP_true⟩
  · rintro ⟨i, h_bound, hP⟩
    have hi_lt : i < s.length + 1 := by
      have : i ≤ s.length := by omega
      omega
    have hi_mem : i ∈ List.range (s.length + 1) :=
      List.mem_range.mpr hi_lt
    have h_bound_true : (i + len ≤ s.length : Bool) = true := by
      simpa using h_bound
    have h_and_true : (i + len ≤ s.length && P (((s.drop i).take len).data)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨h_bound_true, hP⟩
    exact ⟨i, hi_mem, h_and_true⟩

/-! ## All substrings -/

/-- All nonempty substrings of `s`, collected as a `Finset String`.
Duplicates are removed by the finset; only distinct substrings are kept. -/
def allSubstrings (s : String) : Finset String :=
  Id.run do
    let n := s.length
    let mut ss : Finset String := ∅
    for i in List.range n do
      for len in List.range (n - i) do
        let sub := (s.drop i).take (len.succ)
        ss := ss ∪ {sub}
    return ss

/-- All non-empty contiguous substrings of `s`, returned as a `List String`.
Unlike `allSubstrings` which returns a `Finset` and removes duplicates,
this returns a `List` preserving duplicates — useful when counting substrings
(e.g., "how many substrings satisfy a property"). -/
def substringsOf (s : String) : List String :=
  (List.contiguousSublists s.data).map String.mk

/-- Generate all substrings of `s` starting at position `i` with lengths `1` to `len`.
For example, `substringsFrom "abc" 0 3 = ["a", "ab", "abc"]`. -/
def substringsFrom (s : String) (i len : Nat) : List String :=
  (List.range len).map (fun k => (s.drop i).take (k + 1))

/-- Generate all non‑empty substrings of `s`. Equivalent to `substringsOf`. -/
def substrings (s : String) : List String :=
  (List.range s.length).flatMap (fun i => substringsFrom s i (s.length - i))

/-- Count how many non-empty contiguous substrings of `s` satisfy predicate `p`. -/
def countSubstringsSatisfying (s : String) (p : String → Bool) : Nat :=
  List.countP p (substrings s)

/-- Check whether `t` is a contiguous substring of `s`. Returns `false` if `t` is empty
(unless `s` is also empty, in which case the empty string is vacuously a substring). -/
def isSubstring (s t : String) : Bool :=
  (List.range (s.length + 1)).any (fun i =>
    (List.range (s.length - i + 1)).any (fun j =>
      decide (t = (s.drop i).take j)))

/-- `Prop`-valued predicate: `t` is a contiguous substring of `s`.
Defined via `∃ i l, i + l ≤ s.length ∧ t = (s.drop i).take l`.
For the `Bool` version, see `isSubstring`. -/
def IsSubstring (t s : String) : Prop :=
  ∃ i l : Nat, i + l ≤ s.length ∧ t = (s.drop i).take l

/-- A string `t` is in `substringsOfMinLength s k` iff `t.length ≥ k` and `t` is a
contiguous substring of `s`. This is the high-level characterization: filtered by minimum length. -/
lemma mem_substringsOfMinLength_iff_length_ge_and_IsSubstring (t s : String) (k : Nat) :
    t ∈ substringsOfMinLength s k ↔ (t.length ≥ k ∧ IsSubstring t s) := by
  rw [mem_substringsOfMinLength_iff]
  simp only [IsSubstring]
  constructor
  · rintro ⟨i, hi, len, hlen, hlenk, heq⟩
    have hlenle : len ≤ s.length - i := Nat.le_of_lt_succ hlen
    have hbound : i + len ≤ s.length := by omega
    constructor
    · rw [heq]
      rw [substr_length_eq_of_le s i len hlenle]
      exact hlenk
    · exact ⟨i, len, hbound, heq⟩
  · rintro ⟨hlenk, i, len, hbound, heq⟩
    have hi_lt : i < s.length + 1 := by omega
    have hlen_lt : len < s.length - i + 1 := by omega
    have hlenk' : len ≥ k := by
      have hle : ((s.drop i).take len).length ≤ len := by
        simpa [substr] using substr_length_le s i len
      -- heq : t = (s.drop i).take len
      rw [← heq] at hle
      omega
    -- heq : t = (s.drop i).take len, need t = substr s i len
    have heq' : t = substr s i len := by
      simpa [substr] using heq
    exact ⟨i, hi_lt, len, hlen_lt, hlenk', heq'⟩

/-! ## Substring occurrence at position -/

/-- Count occurrences of substring `sub` in string `s`, counting overlapping
occurrences (each position `i` where `isSubstringAt s sub i` holds is counted).

Returns `1` for the empty substring (by convention, the empty string occurs once). -/
def countSubstringOccurrences (s sub : String) : Nat :=
  if sub = "" then 1 else
    (List.range s.length).foldl
      (fun acc i => if isSubstringAt s sub i then acc + 1 else acc) 0

/-- `Bool`-valued version of `isSubstringAt`. Checks whether substring `sub` occurs
at position `i` in `s`. Useful with `List.filter` and other `Bool`-based APIs. -/
def isSubstringAtBool (s sub : String) (i : Nat) : Bool :=
  decide (i + sub.length ≤ s.length) && ((s.drop i).take sub.length == sub)

/-- Find all starting positions where `sub` occurs as a contiguous substring of `s`,
including overlapping occurrences. Returns a `List Nat` of indices in increasing order.
For example, `findSubstringOccurrences "ababa" "aba" = [0, 2]`.

This is the "find all" counterpart of `countSubstringOccurrences`. -/
def findSubstringOccurrences (s sub : String) : List Nat :=
  (List.range (s.length + 1)).filter (isSubstringAtBool s sub)

end String


namespace String


/-! ## Substring extraction utilities -/

/-- Extract the substring after a prefix, trimming whitespace.
Returns `(s.drop pref.length).trim`. If `s` does not start with `pref`,
the behavior is still well-defined — it drops `pref.length` characters
and trims the result regardless. -/
def textAfterPrefix (pref : String) (s : String) : String :=
  (s.drop pref.length).trim

/-- The length of a `slice` is `len` when the slice fits within the string. -/
theorem slice_length (s : String) (start len : Nat) (h : start + len ≤ s.length) :
    (s.slice start len).length = len := by
  unfold slice
  rw [String.length_mk, List.length_take, List.length_drop]
  have hdlen : s.data.length = s.length := rfl
  rw [hdlen]
  have hstart : start ≤ s.length := by omega
  have hlen_le : len ≤ s.length - start := by
    rw [Nat.le_sub_iff_add_le hstart]
    omega
  exact Nat.min_eq_left hlen_le

/-- If `k < s.length`, then taking the first `k` characters of `s` yields a string of length `k`. -/
lemma length_take_of_lt (s : String) (k : Nat) (hk_lt : k < s.length) : (s.take k).length = k := by
  have h_data : (s.take k).data = List.take k s.data := String.data_take s k
  calc
    (s.take k).length = ((s.take k).data).length := rfl
    _ = (List.take k s.data).length := by rw [h_data]
    _ = min k (s.data.length) := List.length_take _ _
    _ = min k (s.length) := rfl
    _ = k := Nat.min_eq_left (Nat.le_of_lt hk_lt)

lemma take_zero (s : String) : s.take 0 = "" := by
  rw [String.take_eq s 0]
  simp

/-- `(s.take k).length = k` when `k ≤ s.length`. -/
lemma take_length_eq_of_le (s : String) (k : Nat) (h : k ≤ s.length) : (s.take k).length = k := by
  rw [String.take_eq s k]
  simp [h]

/-- Nested `take` composition for `String`: `(s.take m).take n = s.take (min m n)`.
This is the string analog of `List.take_take`. -/
lemma take_take (s : String) (m n : Nat) : (s.take m).take n = s.take (min m n) := by
  apply String.ext
  simp [String.data_take, List.take_take]
  omega

/-- Nested `take` reduces to the inner `take` when the inner length does not exceed the outer.
That is, `(s.take m).take n = s.take n` when `n ≤ m`.
This is a corollary of `take_take`. -/
lemma take_take_eq_take_of_le (s : String) (m n : Nat) (h : n ≤ m) : (s.take m).take n = s.take n := by
  rw [take_take, min_eq_right h]

/-- If both `u` and `acc` are prefixes of `s` (i.e. `s.take u.length = u` and
`s.take acc.length = acc`), and `u.length ≤ acc.length`, then `u` is a prefix
of `acc` (i.e. `u = acc.take u.length`). -/
lemma prefix_of_prefix_length_le (s acc u : String) (hacc : s.take acc.length = acc)
    (hu : s.take u.length = u) (hle : u.length ≤ acc.length) : u = acc.take u.length := by
  calc
    u = s.take u.length := hu.symm
    _ = (s.take acc.length).take u.length := by
      rw [take_take_eq_take_of_le s acc.length u.length hle]
    _ = acc.take u.length := by rw [hacc]

/-- The length of `s.take n` is the minimum of `n` and `s.length`.
This is the string analog of `List.length_take`. -/
lemma length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  rw [String.take_eq, String.mk_length, List.length_take, String.length_data]

/-- Taking `(t.take k).length` characters from `t` gives the same result as taking `k` characters.
This is a key identity for normalizing take lengths: the length of the taken prefix
is always enough to recover the full prefix. For example,
`t.take ((t.take 5).length) = t.take 5` even when `t.length < 5`. -/
lemma take_take_length_eq_take (t : String) (k : Nat) : t.take ((t.take k).length) = t.take k := by
  rw [length_take t k]
  by_cases hk : k ≤ t.length
  · rw [min_eq_left hk]
  · have ht_len : t.length ≤ k := by omega
    have htake_k_all : t.take k = t := by
      apply String.ext
      simp [String.data_take, List.take_of_length_le (by simpa [String.length_data] using ht_len)]
    have htake_len_all : t.take (t.length) = t := by
      apply String.ext
      simp [String.data_take, List.take_of_length_le (le_refl _)]
    rw [min_eq_right ht_len, htake_k_all, htake_len_all]

/-- The length of `(s.take k) ++ t` is `(s.take k).length + t.length`.
This is immediate from `String.length_append` but is a convenient rewrite lemma. -/
lemma length_take_append (s t : String) (k : Nat) :
    ((s.take k) ++ t).length = (s.take k).length + t.length := by
  simp

/-- If `k ≤ s.length`, then `((s.take k) ++ t).length = k + t.length`.
Combines `length_take_append` with `take_length_eq_of_le`. -/
lemma length_take_append_of_le (s t : String) (k : Nat) (h : k ≤ s.length) :
    ((s.take k) ++ t).length = k + t.length := by
  rw [length_take_append, take_length_eq_of_le s k h]

/-- If `t.length ≤ n` and `n - t.length ≤ s.length`, then appending `t` after taking
`n - t.length` characters from the front of `s` yields a string of length `n`.
This captures the truncated-string pattern: truncate `s` to make room for `t`. -/
lemma length_take_sub_append (s t : String) (n : Nat) (ht_len : t.length ≤ n) (h_take : n - t.length ≤ s.length) :
    ((s.take (n - t.length)) ++ t).length = n := by
  rw [length_take_append_of_le s t (n - t.length) h_take, Nat.sub_add_cancel ht_len]

/-- If `n ≤ s.length` and `n + suffix.length ≤ max_len`, then `(s.take n ++ suffix).length ≤ max_len`.
This is the inequality variant of `length_take_append_of_le` — useful when only an upper bound is needed
rather than exact equality. -/
lemma take_append_length_le (s suffix : String) (n max_len : Nat) (hn : n ≤ s.length)
    (hnmax : n + suffix.length ≤ max_len) : (s.take n ++ suffix).length ≤ max_len := by
  calc
    (s.take n ++ suffix).length = (s.take n).length + suffix.length := String.length_append _ _
    _ = n + suffix.length := by rw [take_length_eq_of_le s n hn]
    _ ≤ max_len := hnmax

/-- The length of `s.take n` is bounded by `s.length`. -/
lemma take_length_le_source (s : String) (n : Nat) : (s.take n).length ≤ s.length := by
  rw [String.take_eq s n]
  simp

/-- If `s.take n = q`, then `q` has length at most `s.length`. -/
lemma length_le_of_take_eq (s q : String) (n : Nat) (h : s.take n = q) : String.length q ≤ String.length s := by
  have hlen := take_length_le_source s n
  rw [h] at hlen
  exact hlen

/-- If `t.take s.length = s`, then `s.length ≤ t.length`.
This follows because taking `s.length` characters from `t` produces `s`,
so `t` must have at least `s.length` characters. -/
lemma length_ge_of_take_eq (s t : String) (h : t.take s.length = s) : s.length ≤ t.length := by
  by_contra! hlt
  have hdata_lt : t.data.length < s.length := by simpa using hlt
  have hdata_le : t.data.length ≤ s.length := Nat.le_of_lt hdata_lt
  have htake_all : t.take s.length = t := by
    apply String.ext
    simp [String.data_take, List.take_of_length_le hdata_le]
  rw [htake_all] at h
  have hlen_eq : s.length = t.length := by
    simpa using congrArg (·.length) h.symm
  rw [hlen_eq] at hlt
  exact lt_irrefl _ hlt

/-- Taking all remaining characters after dropping `i` is the same as just dropping `i`.
That is, `(s.drop i).take (s.length - i) = s.drop i`. -/
lemma drop_take_all (s : String) (i : Nat) : (s.drop i).take (s.length - i) = s.drop i := by
  apply String.ext
  rw [String.data_take, String.data_drop]
  have : s.data.length = s.length := rfl
  rw [← this]
  exact List.take_drop_eq_drop s.data i

/-- If `(text.drop i).take s.length = s` and `i` is in range (`i < text.length.succ`),
then `s.length + i ≤ text.length`. This bound is needed for range membership reasoning
in substring existence proofs — it guarantees that the substring `s` fits within
the remaining space after position `i`. -/
lemma length_bound_of_take_eq (s text : String) (i : Nat)
    (hi : i < text.length.succ)
    (h_eq : (text.drop i).take s.length = s) : s.length + i ≤ text.length := by
  have hi_le : i ≤ text.length := by omega
  have h_drop_len : (text.drop i).length = text.length - i := by
    rw [String.drop_eq, String.mk_length, List.length_drop, String.length_data]
  have h_take_len_le : s.length ≤ (text.drop i).length := by
    calc
      s.length = ((text.drop i).take s.length).length := by rw [h_eq]
      _ ≤ (text.drop i).length := take_length_le_source (text.drop i) s.length
  rw [h_drop_len] at h_take_len_le
  omega

/-- `s.take i ++ s.drop i = s` — taking the first `i` characters and appending the rest
reconstructs the original string. This is the string analog of `List.take_append_drop`. -/
lemma take_append_drop (s : String) (i : Nat) : s.take i ++ s.drop i = s := by
  ext
  simp [String.data_append, String.data_take, String.data_drop, List.take_append_drop]

/-- The length of `s.drop n` is `s.length - n`.
This is the string analog of `List.length_drop`. -/
lemma length_drop (s : String) (n : Nat) : (s.drop n).length = s.length - n := by
  rw [String.drop_eq, String.mk_length, List.length_drop, String.length_data]

/-- If `0 < n` and `n < s.length`, then dropping `n` characters yields a strictly
shorter string. Useful for termination proofs. -/
lemma length_drop_lt (s : String) (n : Nat) (hn_pos : 0 < n) (hn_lt : n < s.length) :
    (s.drop n).length < s.length := by
  rw [length_drop]
  omega

/-- For a non-empty string, its length equals one plus the length after dropping the first
character. When `s = ""`, the equality does not hold because `("".drop 1).length = 0`
while `1 + 0 ≠ 0`. This lemma bridges `s.length` and `(s.drop 1).length` for non-empty
strings, and is useful when reasoning about recursive string processing (e.g., scanning
the first character and recursing on the tail).

For example, `"abc".length = 1 + ("abc".drop 1).length` (i.e., `3 = 1 + 2`). -/
lemma length_eq_one_add_drop_one_of_ne_empty {s : String} (h : s ≠ "") : s.length = 1 + (s.drop 1).length := by
  have hpos : 1 ≤ s.length := by
    have hlen_pos : s.length > 0 := length_pos_of_ne_empty s h
    omega
  calc
    s.length = (s.length - 1) + 1 := by rw [Nat.sub_add_cancel hpos]
    _ = 1 + (s.length - 1) := by rw [add_comm]
    _ = 1 + (s.drop 1).length := by rw [← length_drop s 1]

/-! ## `take` equality ↔ data `take` equality

These lemmas relate equality of `String.take` to equality of the underlying
`List.take` on the character data. This is useful when translating between
string-level and character-list-level reasoning about prefixes.
-/

/-- If two strings' data satisfy the `take` equality at the data level, then the strings
themselves satisfy the `take` equality at the string level. -/
lemma take_eq_of_data_take_eq {s t : String}
    (h : s.data.take t.data.length = t.data) : s.take t.length = t := by
  apply String.ext
  simpa [String.data_take] using h

/-- If `s.data.take n = d` at the `List` level, then `s.take n = String.mk d` at the `String` level.
This generalizes `take_eq_of_data_take_eq` by allowing the right-hand side to be an arbitrary
character list rather than the data of a specific string. -/
lemma take_eq_mk_of_data_take_eq {s : String} {n : Nat} {d : List Char}
    (h : s.data.take n = d) : s.take n = String.mk d := by
  calc
    s.take n = String.mk (s.data.take n) := by rw [String.take_eq]
    _ = String.mk d := by rw [h]

/-- If two strings satisfy the string-level `take` equality, their underlying data do too,
at the corresponding data-length positions. -/
lemma data_take_eq_of_take_eq {s t : String}
    (h : s.take t.length = t) : s.data.take t.data.length = t.data := by
  have := congrArg String.data h
  simpa [String.data_take] using this

/-- If `s.take n = t` at the `String` level, then `s.data.take n = t.data` at the `List` level.
This generalizes `data_take_eq_of_take_eq` by allowing an arbitrary `n` rather than `t.length`. -/
lemma data_take_eq_of_take_eq_n {s t : String} {n : Nat}
    (h : s.take n = t) : s.data.take n = t.data := by
  rw [String.take_eq s n] at h
  have h' := congrArg String.data h
  simpa using h'

/-- If a character list `l` is a prefix of `w.data`, then taking `l.length` characters
from `w` yields `String.mk l`. This bridges `List` prefix relations to `String.take`. -/
lemma take_eq_of_data_prefix (l : List Char) (w : String) (h : l <+: w.data) :
    w.take l.length = String.mk l := by
  rw [List.prefix_iff_eq_take] at h
  apply String.ext
  calc
    (w.take l.length).data = (w.data).take l.length := by simp
    _ = l := by rw [← h]

/-- If taking `s.length` characters from `w` gives `s`, then `s.data` is a prefix of
`w.data`. This is the converse of `take_eq_of_data_prefix` for the string-to-string case. -/
lemma data_prefix_of_take_eq (s w : String) (h : w.take s.length = s) :
    s.data <+: w.data := by
  rw [List.prefix_iff_eq_take]
  calc
    s.data = (w.take s.length).data := by rw [h]
    _ = (w.data).take s.length := by simp
    _ = (w.data).take (s.data.length) := rfl

/-! ## Append and Take lemmas -/

/-- For any strings `s` and `t`, taking the prefix of length `s.length` from `s ++ t` yields `s`. -/
lemma take_append_left (s t : String) : (s ++ t).take s.length = s := by
  apply String.ext
  simp [List.take_append]

/-- If a suffix has positive length, appending it to a prefix produces a string
    strictly longer than the prefix alone. -/
lemma length_append_gt_of_length_pos {s t : String} (hpos : t.length > 0) :
    (s ++ t).length > s.length := by
  have hlen_app : (s ++ t).length = s.length + t.length := by simp
  omega

/-- If the first `n` characters of `s` equal `t`, then `s` can be written as `t` followed
by some suffix (specifically, `s.drop n`). This generalizes `take_append_drop` into a
useful ∃-quantified form for prefix decomposition. -/
lemma exists_suffix_of_take_eq (s : String) (n : Nat) (t : String) (h : s.take n = t) :
    ∃ suffix, s = t ++ suffix := by
  refine ⟨s.drop n, ?_⟩
  calc
    s = s.take n ++ s.drop n := (take_append_drop s n).symm
    _ = t ++ s.drop n := by rw [h]

/-- For any strings `pref` and `result`, either `pref` is a prefix of `result`
(i.e., `∃ err, result = pref ++ err`) or the first `pref.length` characters of
`result` differ from `pref`. This is a convenient case-split lemma for prefix checking:
use `rcases prefix_or_take_ne pref result with h | h` to branch on whether `pref`
is a prefix of `result`. -/
lemma prefix_or_take_ne (pref result : String) :
    (∃ err, result = pref ++ err) ∨ (result.take pref.length ≠ pref) := by
  by_cases h : result.take pref.length = pref
  · left; exact exists_suffix_of_take_eq result pref.length pref h
  · right; exact h


end String


namespace String

/-! ## Find substring position

Finds the first occurrence of a substring in a string, scanning from left to right.
Returns `Int.ofNat k` for the position `k` if found, or `-1` if not found.
This is the `Int`-returning convention common in contest problems; for an
`Option Nat` version, use `Option`-wrapping yourself (`findSubstring main sub = -1` ↔ none). -/

/-- Scan `main_string` from position `i` with `remaining` steps to find the first
occurrence of `sub_string`. Returns `Int.ofNat k` where `k ≥ i` is the first matching
position, or `-1` if no match is found in the scan range. -/
def findSubstringAux (main_string sub_string : String) (i remaining : Nat) : Int :=
  match remaining with
  | 0 => -1
  | r + 1 =>
    if h : i + sub_string.length ≤ main_string.length then
      if ((main_string.drop i).take sub_string.length) = sub_string then
        Int.ofNat i
      else
        findSubstringAux main_string sub_string (i + 1) r
    else
      -1

/-- Find the first occurrence of `sub_string` in `main_string`.
Returns `Int.ofNat k` for the first position `k` where the substring matches,
or `-1` if `sub_string` does not occur. -/
def findSubstring (main_string sub_string : String) : Int :=
  findSubstringAux main_string sub_string 0 main_string.length

/-! ### Evaluation lemmas for `findSubstringAux` -/

/-- When `remaining = 0`, the search immediately returns `-1` (fuel exhausted). -/

lemma findSubstringAux_eq_neg_one_zero (main_string sub_string : String) (i : Nat) :
    findSubstringAux main_string sub_string i 0 = -1 := by
  simp [findSubstringAux]

/-- When the search position is out of bounds (`¬ i + sub.length ≤ main.length`),
`findSubstringAux` returns `-1` regardless of remaining fuel. -/
lemma findSubstringAux_eq_neg_one_of_nobound (main_string sub_string : String) (i remaining : Nat)
    (h_out : ¬ i + sub_string.length ≤ main_string.length) :
    findSubstringAux main_string sub_string i remaining = -1 := by
  induction' remaining with r ih generalizing i
  · simp [findSubstringAux]
  · simp [findSubstringAux, h_out]

/-- When a match is found at position `i` within bounds and there is remaining fuel,
`findSubstringAux` returns `Int.ofNat i`. -/
lemma findSubstringAux_eq_ofNat_of_match (main_string sub_string : String) (i r : Nat)
    (h_bound : i + sub_string.length ≤ main_string.length)
    (h_match : ((main_string.drop i).take sub_string.length) = sub_string) :
    findSubstringAux main_string sub_string i (r + 1) = Int.ofNat i := by
  simp [findSubstringAux, h_bound, h_match]

/-- When no match at position `i` (within bounds, fuel remaining), `findSubstringAux`
recurses to position `i + 1` with decremented fuel. -/
lemma findSubstringAux_eq_recurse (main_string sub_string : String) (i r : Nat)
    (h_bound : i + sub_string.length ≤ main_string.length)
    (h_nomatch : ¬ ((main_string.drop i).take sub_string.length) = sub_string) :
    findSubstringAux main_string sub_string i (r + 1) =
      findSubstringAux main_string sub_string (i + 1) r := by
  simp [findSubstringAux, h_bound, h_nomatch]

/-- Characterization lemma for `findSubstringAux`.
Scans from position `i` with `remaining` steps available (must satisfy
`main_string.length ≤ i + remaining` to ensure all positions are covered).
Given `h_len : 1 ≤ sub_string.length`, the result satisfies:
either returns `-1` and no position `j ≥ i` matches, or returns `Int.ofNat k`
where `k ≥ i` is the first matching position. -/
lemma findSubstringAux_spec (main_string sub_string : String) (h_len : 1 ≤ sub_string.length)
    (i remaining : Nat) (h_remaining : main_string.length ≤ i + remaining) :
    (findSubstringAux main_string sub_string i remaining = -1 ∧
      ∀ j, i ≤ j → j + sub_string.length ≤ main_string.length →
        ((main_string.drop j).take sub_string.length) ≠ sub_string) ∨
    (∃ k, i ≤ k ∧ k + sub_string.length ≤ main_string.length ∧
      ((main_string.drop k).take sub_string.length) = sub_string ∧
      (∀ j, i ≤ j → j < k → ((main_string.drop j).take sub_string.length) ≠ sub_string) ∧
      findSubstringAux main_string sub_string i remaining = Int.ofNat k) := by
  induction' remaining with r IH generalizing i
  · -- base: remaining = 0
    have hi_ge : main_string.length ≤ i := by omega
    left
    refine ⟨by simp [findSubstringAux], ?_⟩
    intro j hij hbound
    have : main_string.length ≤ j := le_trans hi_ge hij
    omega
  · -- step: remaining = r+1
    have h_unfold : findSubstringAux main_string sub_string i (r + 1) =
        (if h : i + sub_string.length ≤ main_string.length then
          if ((main_string.drop i).take sub_string.length) = sub_string then
            Int.ofNat i
          else
            findSubstringAux main_string sub_string (i + 1) r
        else -1) := by
      simp [findSubstringAux]
    rw [h_unfold]
    split
    · -- hbound: i + sub_string.length ≤ main_string.length
      rename_i hbound
      split
      · -- match at i
        rename_i hmatch
        right
        refine ⟨i, le_refl i, hbound, hmatch, ?_, rfl⟩
        intro j hij hlt
        exfalso; omega
      · -- no match at i
        rename_i hmatch
        have h_next_remaining : main_string.length ≤ (i + 1) + r := by omega
        have h_ih := IH (i + 1) h_next_remaining
        rcases h_ih with (⟨hr_eq, h_all⟩ | ⟨k, hk_i, hk_bound, hk_match_val, hk_first, hr_eq⟩)
        · -- recursive call returned -1
          left
          refine ⟨hr_eq, Logic.forall_ge_extend_left_imp i h_all (λ _ => hmatch)⟩
        · -- recursive call found match at k ≥ i+1
          right
          refine ⟨k, by omega, hk_bound, hk_match_val,
            Logic.forall_ge_extend_left_imp i hk_first (λ _ => hmatch), hr_eq⟩
    · -- hbound: ¬ i + sub_string.length ≤ main_string.length
      rename_i hbound
      left
      refine ⟨rfl, ?_⟩
      intro j hij hbound_j
      omega

/-- Characterization of `findSubstring`: either returns `-1` and no position matches,
or returns `Int.ofNat k` where `k` is the first matching position. -/
lemma findSubstring_spec (main_string sub_string : String) (h_len : 1 ≤ sub_string.length) :
    (findSubstring main_string sub_string = -1 ∧
      ∀ j, j + sub_string.length ≤ main_string.length →
        ((main_string.drop j).take sub_string.length) ≠ sub_string) ∨
    (∃ k, k + sub_string.length ≤ main_string.length ∧
      ((main_string.drop k).take sub_string.length) = sub_string ∧
      (∀ j, j < k → ((main_string.drop j).take sub_string.length) ≠ sub_string) ∧
      findSubstring main_string sub_string = Int.ofNat k) := by
  unfold findSubstring
  have h_remaining : main_string.length ≤ 0 + main_string.length := by omega
  have h_spec := findSubstringAux_spec main_string sub_string h_len 0 main_string.length h_remaining
  rcases h_spec with (h_left | h_right)
  · left
    rcases h_left with ⟨hr_eq, h_all⟩
    exact ⟨hr_eq, λ j hi => h_all j (Nat.zero_le _) hi⟩
  · right
    rcases h_right with ⟨k, _, hk_bound, hk_match, hk_first, hr_eq⟩
    exact ⟨k, hk_bound, hk_match, λ j hj_lt => hk_first j (Nat.zero_le _) hj_lt, hr_eq⟩

/-! ## Find all substring indices

Find all starting indices of a substring in a string. Returns a list of natural numbers
`i` such that the substring of `S` starting at `i` and of length `T.length` equals `T`.
Contrast with `findSubstring` which returns only the first occurrence (as `Int`). -/

/-- Find all starting indices of substring `T` in string `S`.
Returns a list of natural numbers `i` such that the substring of `S`
starting at `i` and of length `T.length` equals `T`. -/
def findSubstringIndices (S T : String) : List Nat :=
  let max_i := S.length - T.length
  List.range (max_i + 1) |>.filter (λ i => decide ((S.drop i).take T.length = T))

end String


namespace String

/-! ## File extension extraction -/

/-- Extract the file extension from a filename: the substring after the last `'.'`.
Returns the empty string if no `'.'` is present.
For example, `getExtension "hello.txt" = "txt"` and `getExtension "Makefile" = ""`. -/
def getExtension (fname : String) : String :=
  let comps := fname.split (fun c => c = '.')
  if comps.length = 1 then "" else comps.getLast!

end String

namespace String

/-! ## Suffix check -/

/-- Boolean check that `s` is a suffix of `t`. -/
def isSuffixOf (s t : String) : Bool :=
  let m := s.length
  let n := t.length
  if _h : m ≤ n then
    t.drop (n - m) == s
  else
    false

/-- Check if a string starts with any of the given prefixes.
For example, `startsWithAny "# TODO: cleanup" ["#", "//"] = true`. -/
def startsWithAny (s : String) (prefixes : List String) : Bool :=
  prefixes.any (s.startsWith ·)

/-- Check if a string ends with any suffix from a list.
For example, `endsWithAny "hello.org" [".com", ".org", ".net"] = true`. -/
def endsWithAny (s : String) (suffixes : List String) : Bool :=
  suffixes.any (fun sfx => s.takeRight sfx.length = sfx)

/-- If `s` ends with `suffix`, replaces that suffix with `replacement` and returns `some`.
Otherwise returns `none`.

For example:
* `replaceSuffix "day" "week" "birthday" = some "birthweek"`
* `replaceSuffix "ing" "ed" "running" = some "runned"`
* `replaceSuffix "xyz" "" "abc" = none` -/
def replaceSuffix (suffix replacement s : String) : Option String :=
  if s.takeRight suffix.length = suffix then
    some (s.dropRight suffix.length ++ replacement)
  else
    none

/-- Prop-valued suffix check: `HasSuffix s suffix` holds when `suffix` is a suffix of `s`.
This is the `Prop` counterpart of `isSuffixOf` (which is `Bool`-valued).
For example, `HasSuffix "hello" "lo"` holds because `"lo"` is the ending of `"hello"`. -/
def HasSuffix (s suffix : String) : Prop :=
  s.length ≥ suffix.length ∧ s.takeRight suffix.length = suffix

/-- Decidable instance for `HasSuffix`, so it can be used in `if` conditions
and `by_cases` reasoning. -/
instance (s suffix : String) : Decidable (HasSuffix s suffix) :=
  inferInstanceAs (Decidable (s.length ≥ suffix.length ∧ s.takeRight suffix.length = suffix))

/-- `ensureSuffix s suffix` returns `s` if `suffix` is already a suffix of `s`,
otherwise appends `suffix` to `s`. For example,
`ensureSuffix "hello" "lo" = "hello"` and `ensureSuffix "hello" "x" = "hellox"`. -/
def ensureSuffix (s : String) (suffix : String) : String :=
  if HasSuffix s suffix then s else s ++ suffix

/-- If `suffix` is already a suffix of `s`, then `ensureSuffix s suffix = s`. -/
lemma ensureSuffix_eq_self (s suffix : String) (h : HasSuffix s suffix) : ensureSuffix s suffix = s := by
  unfold ensureSuffix; simp [h]

/-- If `suffix` is not a suffix of `s`, then `ensureSuffix s suffix = s ++ suffix`. -/
lemma ensureSuffix_eq_append (s suffix : String) (h : ¬ HasSuffix s suffix) : ensureSuffix s suffix = s ++ suffix := by
  unfold ensureSuffix; simp [h]

/-! ## Prefix and suffix checks -/

/-- Check if a string has a given prefix of length `n` and a non-empty suffix after it.
This is a general helper that works for any `n` and any `pref`.
For example:
* `checkPrefixNotEmpty "http://example.com" 7 "http://" = true`
* `checkPrefixNotEmpty "http://" 7 "http://" = false` (suffix is empty)
* `checkPrefixNotEmpty "https://x" 7 "http://" = false` (prefix mismatch) -/
def checkPrefixNotEmpty (s : String) (n : Nat) (pref : String) : Bool :=
  s.take n = pref && s.drop n ≠ ""

/-- When the prefix matches, `checkPrefixNotEmpty` reduces to checking whether the suffix
is non-empty. This lemma works for any string `s`, any natural number `n`, and any prefix. -/
lemma checkPrefixNotEmpty_of_match {s : String} {n : Nat} {pref : String} (h : s.take n = pref) :
    checkPrefixNotEmpty s n pref = (s.drop n ≠ "") := by
  simp [checkPrefixNotEmpty, h]

/-- Check whether `p` is both a prefix and a suffix of `s`.
This checks three conditions: `p.length ≤ s.length`, the prefix of `s` of length
`p.length` equals `p`, and the suffix of `s` of length `p.length` equals `p`.
For example, `isPrefixAndSuffix "ab" "abab" = true` and
`isPrefixAndSuffix "ab" "abcd" = false`. -/
def isPrefixAndSuffix (p s : String) : Bool :=
  decide (p.length ≤ s.length ∧
    s.take p.length = p ∧
    s.drop (s.length - p.length) = p)

/-- The empty string is a prefix of every string. -/

lemma isPrefixOf_empty (s : String) : "".isPrefixOf s := by
  unfold String.isPrefixOf String.substrEq String.substrEq.loop String.endPos String.utf8ByteSize
  simp

/-! ## String distance / comparison -/

/-- Number of positions at which two strings differ (Hamming distance).
Uses `List.countMismatches` on the underlying character lists;
if the strings have different lengths, extra characters are ignored. -/
def diffCount (a b : String) : Nat :=
  List.countMismatches a.data b.data

end String


namespace String

/-! # Prefix operations on strings

This module provides operations for finding the longest prefix match
in a list of strings against a target, along with correctness predicates and lemmas.

## Main definitions
* `hasPrefixAndMore s n pref` — `s` starts with `pref` (of known length `n`) and has more content after it
* `IsMaximalPrefix words target r` — `r` is maximal among `words` as a prefix of `target`
* `longestPrefix words target` — find the longest word in `words` that is a non-empty prefix of `target`

## Main lemmas
* `hasPrefixAndMore_eq_iff` — expand `hasPrefixAndMore` into constituent propositional checks
* `isMaximalPrefix_nil` — the empty list's maximal prefix is `""`
* `isMaximalPrefix_cons_take_w` — `w` beats all alternatives when it's a nonempty prefix and
  `rest` is either empty or shorter
-/

/-- Check whether a string starts with a given prefix (of known length `n`) and has at least
one character after it.  Returns `true` if `s.take n = pref` and `s.drop n` is nonempty.

For example:
* `hasPrefixAndMore "http://example.com" 7 "http://" = true`
* `hasPrefixAndMore "http://" 7 "http://" = false` (no content after prefix)
* `hasPrefixAndMore "ftp://example" 7 "http://" = false` (wrong prefix) -/
def hasPrefixAndMore (s : String) (n : Nat) (pref : String) : Bool :=
  (s.take n = pref) && (s.drop n).length > 0

/-- Expand `hasPrefixAndMore` into its constituent propositional checks. -/
lemma hasPrefixAndMore_eq_iff (s : String) (n : Nat) (pref : String) :
    s.hasPrefixAndMore n pref = true ↔ (s.take n = pref) ∧ (s.drop n).length > 0 := by
  simp [hasPrefixAndMore]

/-- `IsMaximalPrefix words target r` holds when `r` is a maximal prefix of `target`
among `words`: either `r = ""` (no nonempty prefix exists), or `r ∈ words`,
`r` is a prefix of `target`, and every prefix `w ∈ words` of `target` satisfies
`w.length ≤ r.length`. -/
def IsMaximalPrefix (words : List String) (target : String) (r : String) : Prop :=
  (r = "" ∧ ∀ w ∈ words, ¬ (w ≠ "" ∧ w.isPrefixOf target)) ∨
  (r ∈ words ∧ r.isPrefixOf target ∧
    ∀ w ∈ words, w.isPrefixOf target → w.length ≤ r.length)

/-- Recursively find the longest word in `words` that is a non-empty
prefix of `target`. Returns `""` if no such word exists. -/
def longestPrefix (words : List String) (target : String) : String :=
  match words with
  | [] => ""
  | w :: ws =>
    let rest := longestPrefix ws target
    if h_out : w ≠ "" ∧ w.isPrefixOf target then
      if h_in : rest = "" ∨ rest.length < w.length then w
      else rest
    else
      rest

lemma isMaximalPrefix_nil (target : String) : IsMaximalPrefix [] target "" := by
  left
  constructor
  · rfl
  · intro w h; nomatch h

/-- When `w` is a nonempty prefix of `target` and `rest` is either empty or shorter than `w`,
`w` is maximal among `w :: ws`. -/
lemma isMaximalPrefix_cons_take_w (w : String) (ws : List String) (target : String) (rest : String)
    (h_w_nonempty_prefix : w ≠ "" ∧ w.isPrefixOf target)
    (h_rest_weak : rest = "" ∨ rest.length < w.length)
    (h_rest : IsMaximalPrefix ws target rest) :
    IsMaximalPrefix (w :: ws) target w := by
  rcases h_w_nonempty_prefix with ⟨h_w_ne, h_w_prefix⟩
  right
  refine ⟨?_, h_w_prefix, ?_⟩
  · exact List.Mem.head ws
  · intro w' h_mem h_w'_prefix
    cases h_mem with
    | head =>
      exact le_refl _
    | tail _ h_mem_ws =>
      rcases h_rest with (⟨h_rest_eq, h_no_prefix⟩ | ⟨h_rest_mem, h_rest_prefix, h_rest_max⟩)
      · by_cases h_w'_ne : w' = ""
        · subst h_w'_ne; exact Nat.zero_le _
        · exfalso; exact h_no_prefix w' h_mem_ws ⟨h_w'_ne, h_w'_prefix⟩
      · have h_le_rest := h_rest_max w' h_mem_ws h_w'_prefix
        rcases h_rest_weak with (h_eq | h_lt)
        · rw [h_eq] at h_le_rest
          have h_len_zero : w'.length = 0 := Nat.eq_zero_of_le_zero h_le_rest
          rw [h_len_zero]; exact Nat.zero_le _
        · omega

/-! ### Case-insensitive prefix operations -/

/-- Check if `pref` is a prefix of `s` case-insensitively.
Both strings are lowered before comparison. For example:
* `isPrefixOfCI "Hello world" "hello" = true`
* `isPrefixOfCI "Hello world" "WORLD" = false` (prefix, not suffix)
* `isPrefixOfCI "Hello" "xyz" = false`

This is the case-insensitive counterpart of `String.isPrefixOf`,
analogous to how `caseInsensitiveEq` compares two strings ignoring case. -/
def isPrefixOfCI (s pref : String) : Bool :=
  (pref.toLower).isPrefixOf (s.toLower)

/-- Check if `s` has any of the given prefixes case-insensitively.
Returns `true` iff there exists `p ∈ prefixes` such that `isPrefixOfCI s p`.
For example:
* `hasAnyPrefixCI "Hello world" ["he", "wo"] = true`
* `hasAnyPrefixCI "Hello world" ["wo", "xyz"] = false`
* `hasAnyPrefixCI "" ["a"] = false` -/
def hasAnyPrefixCI (s : String) (prefixes : List String) : Bool :=
  prefixes.any (isPrefixOfCI s)

/-- `hasAnyPrefixCI s prefixes` is true iff there exists a prefix in the list
that `s` starts with case-insensitively. -/

theorem hasAnyPrefixCI_eq_true_iff (s : String) (prefixes : List String) :
    hasAnyPrefixCI s prefixes = true ↔ ∃ p ∈ prefixes, isPrefixOfCI s p := by
  simp [hasAnyPrefixCI, isPrefixOfCI]

/-- `isPrefixOfCI s pref` is true iff the lowered `pref` is a prefix of the lowered `s`. -/

theorem isPrefixOfCI_eq_true_iff (s pref : String) :
    isPrefixOfCI s pref = true ↔ (pref.toLower).isPrefixOf (s.toLower) := by
  simp [isPrefixOfCI]

/-! ### All prefixes of a string -/

/-- The list of all prefixes of `s`: `[s.take 0, s.take 1, ..., s.take s.length]`.
Each prefix is obtained by taking the first `i` characters for `i = 0..s.length`.

This is commonly used in dynamic programming over prefixes (e.g., word break),
where one needs to iterate over all prefix substrings of a given string. -/
def prefixes (s : String) : List String :=
  (List.range (s.length + 1)).map (fun i => s.take i)

/-- The list of all prefixes of `s` has length `s.length + 1`. -/
lemma prefixes_length (s : String) : (prefixes s).length = s.length + 1 := by
  unfold prefixes; simp

end String


namespace String

/-! # Longest Common Prefix (LCP) of Two Strings

This module provides functions and theorems for computing the longest common prefix
of two strings, both as a length (`findCommonPrefixLen`) and as a string (`commonPrefixOfTwo`).

## Main definitions
* `findCommonPrefixLen s1 s2 n` — largest `k ≤ n` such that `s1.take k = s2.take k`
* `commonPrefixOfTwo s1 s2` — the longest common prefix string of `s1` and `s2`

## Main lemmas
* `findCommonPrefixLen_le` — the result does not exceed the search bound
* `findCommonPrefixLen_eq_take` — the takes at the computed length are equal
* `findCommonPrefixLen_maximal` — any common prefix length is bounded by the computed value
* `commonPrefixOfTwo_prefix_s1` / `commonPrefixOfTwo_prefix_s2` — the result is a prefix of each input
* `commonPrefixOfTwo_maximal` — any common prefix is not longer than the computed one
-/

/-- Find the largest `k ≤ n` such that `s1.take k = s2.take k`, searching downward from `n`. -/
def findCommonPrefixLen (s1 s2 : String) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n'+1 =>
    if s1.take (n'+1) = s2.take (n'+1) then
      n'+1
    else
      findCommonPrefixLen s1 s2 n'
termination_by n

lemma findCommonPrefixLen_le (s1 s2 : String) (n : Nat) : findCommonPrefixLen s1 s2 n ≤ n := by
  induction' n with n' ih
  · simp [findCommonPrefixLen]
  · simp [findCommonPrefixLen]
    split
    · omega
    · exact Nat.le_trans ih (Nat.le_succ _)

lemma findCommonPrefixLen_eq_take (s1 s2 : String) (n : Nat) :
    s1.take (findCommonPrefixLen s1 s2 n) = s2.take (findCommonPrefixLen s1 s2 n) := by
  induction' n with n' ih
  · simp [findCommonPrefixLen]
    apply String.ext
    simp
  · simp [findCommonPrefixLen]
    split
    · assumption
    · exact ih

lemma findCommonPrefixLen_maximal (s1 s2 : String) (n k : Nat) (hk : k ≤ n)
    (heq : s1.take k = s2.take k) : k ≤ findCommonPrefixLen s1 s2 n := by
  revert k
  induction n with
  | zero =>
      intro k hk heq
      have hk0 : k = 0 := by omega
      subst hk0; simp [findCommonPrefixLen]
  | succ n' ih =>
      intro k hk heq
      by_cases htake : s1.take (n' + 1) = s2.take (n' + 1)
      · simp [findCommonPrefixLen, htake]
        omega
      · simp [findCommonPrefixLen, htake]
        rcases Nat.eq_or_lt_of_le hk with (rfl | hk_lt)
        · exfalso; exact htake heq
        · apply ih k ?_ heq
          omega

/-- Compute the longest common prefix of two strings. -/
def commonPrefixOfTwo (s1 s2 : String) : String :=
  let maxLen := min s1.length s2.length
  s1.take (findCommonPrefixLen s1 s2 maxLen)

lemma commonPrefixOfTwo_prefix_s1 (s1 s2 : String) :
    s1.take (commonPrefixOfTwo s1 s2).length = commonPrefixOfTwo s1 s2 := by
  dsimp [commonPrefixOfTwo]
  set k := findCommonPrefixLen s1 s2 (min s1.length s2.length) with hk
  have hk_le : k ≤ s1.length := by
    have h := findCommonPrefixLen_le s1 s2 (min s1.length s2.length)
    rw [hk]
    exact Nat.le_trans h (Nat.min_le_left _ _)
  have hlen : (s1.take k).length = k := by
    rw [String.take_eq s1 k]
    simp [hk_le]
  rw [hlen]

lemma commonPrefixOfTwo_prefix_s2 (s1 s2 : String) :
    s2.take (commonPrefixOfTwo s1 s2).length = commonPrefixOfTwo s1 s2 := by
  dsimp [commonPrefixOfTwo]
  set k := findCommonPrefixLen s1 s2 (min s1.length s2.length) with hk
  have h_eq : s1.take k = s2.take k := findCommonPrefixLen_eq_take s1 s2 (min s1.length s2.length)
  have hk_le_s2 : k ≤ s2.length := by
    have h := findCommonPrefixLen_le s1 s2 (min s1.length s2.length)
    rw [hk]
    exact Nat.le_trans h (Nat.min_le_right _ _)
  have hlen2 : (s2.take k).length = k := by
    rw [String.take_eq s2 k]
    simp [hk_le_s2]
  calc
    s2.take (s1.take k).length = s2.take (s2.take k).length := by rw [h_eq]
    _ = s2.take k := by rw [hlen2]
    _ = s1.take k := h_eq.symm

lemma commonPrefixOfTwo_maximal (s1 s2 : String) (t : String)
    (h1 : s1.take t.length = t) (h2 : s2.take t.length = t) :
    t.length ≤ (commonPrefixOfTwo s1 s2).length := by
  dsimp [commonPrefixOfTwo]
  set k := findCommonPrefixLen s1 s2 (min s1.length s2.length) with hk
  have hk_le_s1 : k ≤ s1.length := by
    have h := findCommonPrefixLen_le s1 s2 (min s1.length s2.length)
    rw [hk]
    exact Nat.le_trans h (Nat.min_le_left _ _)
  have hlen_eq : (s1.take k).length = k := by
    rw [String.take_eq s1 k]
    simp [hk_le_s1]
  rw [hlen_eq]
  have ht_le_s1 : t.length ≤ s1.length := by
    rw [← h1]
    rw [String.take_eq s1 t.length]
    simp [List.length_take]
  have ht_le_s2 : t.length ≤ s2.length := by
    rw [← h2]
    rw [String.take_eq s2 t.length]
    simp [List.length_take]
  have ht_le_min : t.length ≤ min s1.length s2.length :=
    Nat.le_min.mpr ⟨ht_le_s1, ht_le_s2⟩
  have heq_take : s1.take t.length = s2.take t.length := by rw [h1, h2]
  exact findCommonPrefixLen_maximal s1 s2 (min s1.length s2.length) t.length ht_le_min heq_take

/-! ## LCP of a list of strings -/

/-- Longest common prefix of a list of strings. Returns the empty string for an empty list,
the sole element for a singleton, and otherwise folds `commonPrefixOfTwo` left-associatively. -/
def lcpList (strs : List String) : String :=
  match strs with
  | [] => ""
  | [s] => s
  | first :: second :: rest =>
    commonPrefixOfTwo first (lcpList (second :: rest))

/-! ## Character-by-character LCP (via `List.commonPrefix`)

This section provides an alternative algorithm for computing the longest common
prefix, based on `List.commonPrefix` from `general.List.PrefixSuffix`. In contrast to
the `commonPrefixOfTwo`/`findCommonPrefixLen` approach above (which searches downward
from the minimum length using `take` equality), the `List.commonPrefix` approach builds
the prefix character by character, making prefix properties easier to prove directly.

The `String`-level wrappers below delegate to the general `List α` theory, keeping
the proofs lightweight.
-/

/-- Compute the longest common prefix of two strings by comparing characters
one by one. Delegates to `List.commonPrefix` on the underlying character data. -/
def commonPrefix (s₁ s₂ : String) : String :=
  String.mk (List.commonPrefix s₁.data s₂.data)


lemma commonPrefix_data_eq (s₁ s₂ : String) : (commonPrefix s₁ s₂).data = List.commonPrefix s₁.data s₂.data := rfl

/-- `commonPrefix s₁ s₂` is a prefix of `s₁`. -/
lemma commonPrefix_prefix_left (s₁ s₂ : String) : (commonPrefix s₁ s₂).data <+: s₁.data :=
  List.commonPrefix_isPrefix_left s₁.data s₂.data

/-- `commonPrefix s₁ s₂` is a prefix of `s₂`. -/
lemma commonPrefix_prefix_right (s₁ s₂ : String) : (commonPrefix s₁ s₂).data <+: s₂.data :=
  List.commonPrefix_isPrefix_right s₁.data s₂.data

/-- If `p` is a prefix of both `s₁` and `s₂`, then `p` is a prefix of `commonPrefix s₁ s₂`. -/
lemma commonPrefix_isPrefix_of_prefix (p s₁ s₂ : String) (hp₁ : p.data <+: s₁.data) (hp₂ : p.data <+: s₂.data) :
    p.data <+: (commonPrefix s₁ s₂).data :=
  List.commonPrefix_isPrefix_maximal p.data s₁.data s₂.data hp₁ hp₂

/-- The length of any common prefix is at most the length of the `commonPrefix` result. -/
lemma commonPrefix_length_le (p s₁ s₂ : String) (hp₁ : p.data <+: s₁.data) (hp₂ : p.data <+: s₂.data) :
    p.data.length ≤ (commonPrefix s₁ s₂).data.length := by
  have h : p.data <+: (commonPrefix s₁ s₂).data := commonPrefix_isPrefix_of_prefix p s₁ s₂ hp₁ hp₂
  exact List.IsPrefix.length_le h

/-! ### Folding `commonPrefix` over a list of strings -/

/-- Fold `commonPrefix` over a list of strings, starting from an initial accumulator.
This computes the common prefix of the accumulator with all strings in the list. -/
def commonPrefixFold (acc : String) (ss : List String) : String :=
  String.mk (List.commonPrefixFold acc.data (ss.map String.data))


lemma commonPrefixFold_data_eq (acc : String) (ss : List String) :
    (commonPrefixFold acc ss).data = List.commonPrefixFold acc.data (ss.map String.data) := rfl

/-- The result of `commonPrefixFold acc ss` is a prefix of `acc`. -/
lemma commonPrefixFold_isPrefix_init (acc : String) (ss : List String) :
    (commonPrefixFold acc ss).data <+: acc.data :=
  List.commonPrefixFold_isPrefix_init acc.data (ss.map String.data)

/-- The result of `commonPrefixFold acc ss` is a prefix of every string in `ss`. -/
lemma commonPrefixFold_isPrefix_mem (acc : String) (ss : List String) (s : String)
    (hs : s ∈ ss) : (commonPrefixFold acc ss).data <+: s.data := by
  have h_mem_data : s.data ∈ ss.map String.data := List.mem_map.mpr ⟨s, hs, rfl⟩
  exact List.commonPrefixFold_isPrefix_mem acc.data (ss.map String.data) s.data h_mem_data

/-- If `p` is a prefix of `acc` and of every string in `ss`, then `p` is a prefix
of the result of `commonPrefixFold acc ss`. -/
lemma commonPrefixFold_isPrefix_maximal (p acc : String) (ss : List String)
    (hp_acc : p.data <+: acc.data) (hp_all : ∀ s ∈ ss, p.data <+: s.data) :
    p.data <+: (commonPrefixFold acc ss).data := by
  have hp_all' : ∀ l ∈ ss.map String.data, p.data <+: l := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨s, hs, rfl⟩
    exact hp_all s hs
  exact List.commonPrefixFold_isPrefix_maximal p.data acc.data (ss.map String.data) hp_acc hp_all'

/-- `commonPrefixFold acc ss` is a prefix of every string in `acc :: ss`. -/
lemma commonPrefixFold_isPrefix_cons (acc : String) (ss : List String) :
    ∀ a, a ∈ acc :: ss → (commonPrefixFold acc ss).data <+: a.data := by
  intro a ha
  by_cases h_eq : a = acc
  · rw [h_eq]
    exact commonPrefixFold_isPrefix_init acc ss
  · have ha_ss : a ∈ ss := by
      simpa [List.mem_cons, h_eq] using ha
    exact commonPrefixFold_isPrefix_mem acc ss a ha_ss

/-- The result of `commonPrefixFold acc ss` has maximal length among common
prefixes of `acc :: ss`. -/
lemma commonPrefixFold_length_maximal (acc : String) (ss : List String) :
    ∀ (p : String), (∀ a, a ∈ acc :: ss → p.data <+: a.data) →
    p.data.length ≤ (commonPrefixFold acc ss).data.length := by
  intro p hp
  have hp_acc : p.data <+: acc.data := hp acc (by simp)
  have hp_rest : ∀ a, a ∈ ss → p.data <+: a.data := by
    intro a ha
    exact hp a (by simp [ha])
  have h_prefix : p.data <+: (commonPrefixFold acc ss).data :=
    commonPrefixFold_isPrefix_maximal p acc ss hp_acc hp_rest
  exact List.IsPrefix.length_le h_prefix

/-! ### LCP of a list of strings -/

/-- Compute the longest common prefix of a list of strings.
Returns `""` for an empty list, otherwise folds `commonPrefix` over the tail
starting from the head. -/
def commonPrefixOfList (words : List String) : String :=
  match words with
  | [] => ""
  | w :: ws => commonPrefixFold w ws

/-- For a nonempty list, `commonPrefixOfList (w :: ws)` is a prefix of every word. -/
lemma commonPrefixOfList_isPrefix_all (w : String) (ws : List String) :
    ∀ a, a ∈ w :: ws → (commonPrefixOfList (w :: ws)).data <+: a.data := by
  simp only [commonPrefixOfList]
  exact commonPrefixFold_isPrefix_cons w ws

/-- For a nonempty list, `commonPrefixOfList` has maximal length among all common
prefixes. -/
lemma commonPrefixOfList_length_maximal (w : String) (ws : List String) :
    ∀ (p : String), (∀ a, a ∈ w :: ws → p.data <+: a.data) →
    p.data.length ≤ (commonPrefixOfList (w :: ws)).data.length := by
  simp only [commonPrefixOfList]
  exact commonPrefixFold_length_maximal w ws

end String

namespace String

/-! ## String LCP (longest common prefix of suffixes) -/

/-- Compute the length of the longest common prefix of the suffixes of `s` starting at
positions `i` and `j`. This is useful for comparing substrings in suffix-based algorithms. -/
def stringLCP (s : String) (i j : Nat) : Nat :=
  List.listLCP (s.toList.drop i) (s.toList.drop j)

/-- String LCP is symmetric. -/
lemma stringLCP_symm (s : String) (i j : Nat) : stringLCP s i j = stringLCP s j i := by
  simp [stringLCP, List.listLCP_symm]

/-! ## All lowercase strings of a given length -/

/-- Generate all strings of length `n` using only lowercase ASCII letters (`'a'`–`'z'`).
Returns a finite list; the number of strings is `26^n`. Useful for exhaustive search over
bounded-length string domains. -/
def allLowerStrings : Nat → List String
  | 0 => [""]
  | n+1 =>
      let prev := allLowerStrings n
      (List.range 26).flatMap (fun k =>
        let c : Char := Char.ofNat (k + 97)
        prev.map (fun s => s.push c))

/-! ## All binary strings of a given length -/

/-- Generate all binary strings of length `n` (strings over `{'0','1'}`) in
lexicographic order. The empty string is the unique binary string of length 0.
For example, `allBinaryStrings 2 = ["00", "01", "10", "11"]`. -/
def allBinaryStrings : Nat → List String
  | 0 => [""]
  | n+1 =>
      let prev := allBinaryStrings n
      (prev.map (fun s => "0" ++ s)) ++ (prev.map (fun s => "1" ++ s))

/-! ## Even/odd character extraction -/

/-- Extract characters at even positions (0-indexed) from a string.
For example, `evenChars "abcd" = ['a','c']`. -/
def evenChars (s : String) : List Char := List.evenPositions s.data

/-- Extract characters at odd positions (0-indexed) from a string.
For example, `oddChars "abcd" = ['b','d']`. -/
def oddChars (s : String) : List Char := List.oddPositions s.data

/-! ## Common prefix length -/

/-- Compute the length of the longest common prefix of two strings.
Compares characters pairwise by zipping the character data,
taking while the pair elements are equal, and returning the length
of the resulting list. -/
def commonPrefixLength (a b : String) : Nat :=
  ((a.data).zip b.data).takeWhile (fun p => p.1 = p.2) |>.length

lemma commonPrefixLength_le_left (a b : String) : commonPrefixLength a b ≤ a.length := by
  unfold commonPrefixLength
  have ha_len : a.length = (a.data).length := rfl
  rw [ha_len]
  have htake : List.length (((a.data).zip b.data).takeWhile (fun p => p.1 = p.2)) ≤
      List.length ((a.data).zip b.data) :=
    List.length_takeWhile_le _ _
  have hzip : List.length ((a.data).zip b.data) ≤ List.length (a.data) := by
    rw [List.length_zip]
    exact Nat.min_le_left _ _
  exact Nat.le_trans htake hzip

lemma commonPrefixLength_le_right (a b : String) : commonPrefixLength a b ≤ b.length := by
  unfold commonPrefixLength
  have hb_len : b.length = (b.data).length := rfl
  rw [hb_len]
  have htake : List.length (((a.data).zip b.data).takeWhile (fun p => p.1 = p.2)) ≤
      List.length ((a.data).zip b.data) :=
    List.length_takeWhile_le _ _
  have hzip : List.length ((a.data).zip b.data) ≤ List.length (b.data) := by
    rw [List.length_zip]
    exact Nat.min_le_right _ _
  exact Nat.le_trans htake hzip

lemma commonPrefixLength_le_min_length (a b : String) : commonPrefixLength a b ≤ Nat.min a.length b.length := by
  rw [Nat.le_min]
  exact ⟨commonPrefixLength_le_left a b, commonPrefixLength_le_right a b⟩

end String
