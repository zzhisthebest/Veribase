import general.Char.Core

namespace Char

/-! ### Balanced parentheses / brackets on `List Char`

These provide a convenient specialization for checking whether a list of characters
is balanced with respect to a given opening/closing character pair (e.g., `'('` and `')'`).
Characters other than `op` and `cl` are ignored (balance unchanged).

This is a char‑friendly wrapper around `List.balancedScan` (in `general/List/Scan.lean`),
which works with an arbitrary weight function `w : α → Int`. -/

/-- Auxiliary function for `charsBalanced`: process list with current balance counter.
Characters matching `op` increment the balance, characters matching `cl` decrement it,
other characters leave the balance unchanged. If the balance ever goes negative, returns `false`.
Otherwise, at the end, checks that the balance is zero. -/
def charsBalancedAux (op cl : Char) : List Char → Int → Bool
  | [], bal => bal = 0
  | c :: cs, bal =>
      let bal' := if c = op then bal + 1 else if c = cl then bal - 1 else bal
      if bal' < 0 then false else charsBalancedAux op cl cs bal'

/-- Check if a list of characters is balanced with respect to given opening/closing characters.
Other characters are ignored (balance unchanged). -/
def charsBalanced (op cl : Char) (t : List Char) : Bool :=
  charsBalancedAux op cl t 0

/-- Step contribution of a character to the classic balanced-parentheses count:
    `'('` contributes `+1`, all other characters contribute `-1`.
    This is the specific weight function for `List.balancedScan` in the
    classic balanced-parentheses problem (only `'('` and `')'`).

    For example:
    * `parenStep '(' = 1`
    * `parenStep ')' = -1`
    * `parenStep 'x' = -1`

    For a parameterized version with arbitrary open/close characters,
    use `charsBalanced`. -/
def parenStep (c : Char) : Int :=
  if c = '(' then 1 else -1

end Char
