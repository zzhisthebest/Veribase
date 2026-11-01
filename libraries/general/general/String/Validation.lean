import Mathlib
import general.List.Parsing
import general.String.CharacterStatistics

namespace String


/-! ## Length range check -/

/-- Check that a string's length is within the inclusive bounds `[lo, hi]`.
    For example, `lengthInRange "abc" 1 5 = true` and `lengthInRange "abc" 4 6 = false`. -/
def lengthInRange (s : String) (lo hi : Nat) : Bool :=
  let len := s.length
  len ≥ lo && len ≤ hi



/-! ### Total length of string list -/

/-- Sum of the lengths of all strings in a list.
`totalLength ["hello", "world"] = 10`. -/
def totalLength (l : List String) : Nat :=
  l.foldl (fun acc w => acc + w.length) 0



end String

namespace String


/-! ## Bracket validation -/

/-- Check whether a string has balanced brackets (`(`, `)`, `[`, `]`, `{`, `}`).
Uses stack-based validation via `List.balancedFold` with the standard bracket-pair mapping.
Non-bracket characters are ignored. -/
def isValidBracket (s : String) : Bool :=
  List.balancedFold Char.bracketPair s.data []

/-- Check whether a string with `(`, `)`, `*` can be a valid parenthesis string,
where `*` can represent `(`, `)`, or empty.
This is a convenience wrapper over `List.parenthesisWildcardBalanced`. -/
def parenthesisWildcardBalanced (s : String) : Bool :=
  List.parenthesisWildcardBalanced s.data

/-- Check whether a string has balanced parentheses: every `'('` is matched
    by a `')'` and the running balance never goes negative.
    Uses `List.balancedScan` with `Char.parenStep` (weight: `'(' → +1`, else `-1`),
    initialized at balance 0.

    Characters other than `'('` and `')'` also contribute `-1`, so this function
    assumes the input contains only `'('` and `')'`. For a parameterized version
    with arbitrary character pairs use `isValidBracket` (stack-based) or
    `Char.charsBalanced` (running-sum with configurable open/close).

    For example:
    * `isBalancedParen "(()())" = true`
    * `isBalancedParen "())(" = false`
    * `isBalancedParen "" = true` (empty is trivially balanced) -/
def isBalancedParen (s : String) : Bool :=
  List.balancedScan Char.parenStep s.data 0

/-- Count the number of distinct letters that appear in both cases in `s`.
A letter is counted once regardless of how many times its variants appear.
Convenience wrapper that operates on `String` instead of `List Char`. -/
def countBothCaseLetters (s : String) : Nat :=
  countDistinctBothCaseLetters s.data

end String
