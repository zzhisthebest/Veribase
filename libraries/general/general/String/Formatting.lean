import Mathlib
import general.String.SplitJoining
import general.String.Substrings

namespace String

/-! ## Fixed-point decimal formatting -/

/-- Format a fixed-point integer value as a string with the given number of fractional digits.
The value is interpreted as `intPart * 10 ^ decimalPlaces + fracPart`.
For example:
* `formatFixedDecimal 2 1234 = "12.34"`
* `formatFixedDecimal 3 5001 = "5.001"`
* `formatFixedDecimal 0 42 = "42"` -/
def formatFixedDecimal (decimalPlaces : Nat) (value : Nat) : String :=
  let divisor := 10 ^ decimalPlaces
  let intPart := value / divisor
  let fracPart := value % divisor
  let fracStr := toString fracPart
  let padZeros := String.mk (List.replicate (decimalPlaces - fracStr.length) '0')
  s!"{intPart}.{padZeros}{fracStr}"

/-! ## Zero-padding

Zero-pad a string with `'0'` characters to a given minimum width.
If the string is already at least as long as `width`, it is returned unchanged.
This is a general string utility; for Nat-specific zero‑padding, see `Nat.zeroPad`. -/

/-- Zero-pad a string with `'0'` characters to a given minimum width.
If `width ≤ s.length`, the string is returned unchanged.
For example:
* `String.zeroPad 5 "ab" = "000ab"`
* `String.zeroPad 2 "abcd" = "abcd"` -/
def zeroPad (width : Nat) (s : String) : String :=
  if s.length < width then
    (String.replicate (width - s.length) '0') ++ s
  else
    s

/-- The length of a zero-padded string is `max width s.length`. -/
lemma zeroPad_length (width : Nat) (s : String) :
    (zeroPad width s).length = max width s.length := by
  unfold zeroPad
  split
  · rename_i h
    rw [String.length_append, String.length_replicate]
    omega
  · have hmax : max width s.length = s.length := by
      omega
    rw [hmax]

/-- If `width ≤ s.length`, zero-padding has no effect. -/
lemma zeroPad_of_le (width : Nat) (s : String) (h : width ≤ s.length) :
    zeroPad width s = s := by
  unfold zeroPad
  simp [h]

/-- Zero-padding to width 0 returns the original string. -/

lemma zeroPad_zero (s : String) : zeroPad 0 s = s := by
  unfold zeroPad; simp

/-! ## Replicate padding length lemmas

These lemmas capture the general pattern of padding a string with `String.replicate`
to reach a target length, optionally with a prefix. They are the key arithmetic facts
used in `zeroPad_length` and similar padding proofs. -/

/-- Padding a string with `String.replicate` to a target length produces a string
of length at least the target. This is the fundamental lemma for `String.replicate`
padding — it says that `replicate (n - s.length) c ++ s` always has length ≥ n,
regardless of whether `s` is already longer than `n` (in which case the replicate
is empty and the inequality holds because `s.length ≥ n`).

For example:
* `(String.replicate (5 - "ab".length) '0' ++ "ab").length ≥ 5`
* `(String.replicate (2 - "abcde".length) '0' ++ "abcde").length ≥ 2` -/
lemma length_replicate_suffix_ge (s : String) (n : Nat) (c : Char) :
    (String.replicate (n - s.length) c ++ s).length ≥ n := by
  simp [String.length_append, String.length_replicate]
  omega

/-- Generalization of `length_replicate_suffix_ge` with an arbitrary prefix string
`pref`. The padding accounts for the prefix length. When `pref = ""`, this reduces
to `length_replicate_suffix_ge`. When `pref = "-"` (single-character prefix), it
captures the pattern of left-padding a signed number representation.

For example:
* `("-" ++ String.replicate (5 - ("ab".length + 1)) '0' ++ "ab").length ≥ 5`
* `("+ " ++ String.replicate (4 - ("1".length + 2)) '0' ++ "1").length ≥ 4` -/
lemma length_prefix_replicate_suffix_ge (pref s : String) (n : Nat) (c : Char) :
    (pref ++ String.replicate (n - (s.length + pref.length)) c ++ s).length ≥ n := by
  simp [String.length_append, String.length_replicate]
  omega

/-! ## Arithmetic operator utilities (string-token level) -/

/-- Recognize the four basic arithmetic operators as string tokens: `"+"`, `"-"`, `"*"`, `"/"`. -/
def isArithOp (t : String) : Bool :=
  t = "+" ∨ t = "-" ∨ t = "*" ∨ t = "/"

/-- Precedence level for arithmetic operators as string tokens:
1 for `+` / `-`, 2 for `*` / `/`, 0 otherwise. -/
def arithPrecedence (op : String) : Nat :=
  match op with
  | "+" => 1
  | "-" => 1
  | "*" => 2
  | "/" => 2
  | _   => 0

/-- Convert a list of arithmetic expression tokens from infix to postfix (RPN)
order using the Shunting Yard algorithm. -/
def shuntingYard (tokens : List String) : List String :=
  let isLeftParen (t : String) : Bool := t = "("
  let isRightParen (t : String) : Bool := t = ")"
  let shouldPop (top cur : String) : Bool := arithPrecedence top ≥ arithPrecedence cur
  List.shuntingCore isLeftParen isRightParen isArithOp shouldPop tokens [] []

end String


namespace String

/-! ## Fixed-point formatting -/

/-- Zero-pad a `Nat` to `width` digits as a string.
For example, `zeroPadNat 2 7 = "07"`, `zeroPadNat 2 15 = "15"`.
If the number already has ≥ `width` digits, it is returned as-is. -/
def zeroPadNat (width : Nat) (n : Nat) : String :=
  let s := toString n
  let padding := (List.replicate (width - s.length) '0').asString
  padding ++ s

/-- Format a `Nat` as a two-digit string, zero-padded if needed.
For example, `formatTwoDigit 7 = "07"`, `formatTwoDigit 15 = "15"`. -/
def formatTwoDigit (n : Nat) : String :=
  if n < 10 then "0" ++ toString n else toString n

/-- Format a fixed-point scaled value as a percentage string with two decimal places.

Assumes `scale` is a multiple of 100 (e.g., `10000` for two decimal places of precision).
The integer part is `val / (scale / 100)` and the fractional part is `val % (scale / 100)`.

For example:
* `formatPercentage 10000 12345 = "123.45%"`
* `formatPercentage 10000 2500 = "25.0%"` -/
def formatPercentage (scale val : Nat) : String :=
  let divisor := scale / 100
  s!"{val / divisor}.{val % divisor}%"

end String

namespace String


/-! ## Formatting key–value pairs -/

/-- Format a list of key-value string pairs into a single string, with configurable
separators. Each pair `(k, v)` is rendered as `k ++ kvSep ++ v`, and consecutive
entries are joined by `sep`. Returns `""` for the empty list. -/
def formatKeyValuePairs (sep kvSep : String) (l : List (String × String)) : String :=
  l.foldr (fun kv acc => kv.1 ++ kvSep ++ kv.2 ++ (if acc = "" then "" else sep ++ acc)) ""

/-- `formatKeyValuePairs` on an empty list returns the empty string. -/

lemma formatKeyValuePairs_nil (sep kvSep : String) : formatKeyValuePairs sep kvSep [] = "" := rfl

/-- Format an association list of key‑value pairs as a comma‑separated `"Key: Value"` string.
For example, `formatFields [("Make", "Toyota"), ("Color", "Red")] = "Make: Toyota, Color: Red"`. -/
def formatFields (fields : List (String × String)) : String :=
  formatKeyValuePairs ", " ": " fields


/-! ### Formatting pairs -/

/-- Format a pair of strings as `"key=value"`.
For example, `pairToEq ("name", "Alice") = "name=Alice"`. -/
def pairToEq (p : String × String) : String :=
  p.fst ++ "=" ++ p.snd


end String
