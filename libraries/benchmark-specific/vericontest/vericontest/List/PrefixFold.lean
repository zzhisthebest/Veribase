import Mathlib

open List

/-!
# Prefix Fold — cumulative folding over list prefixes

`prefixFold f xs init i` folds `f` over `init` and `xs[1]!, …, xs[i]!`.
Returns `init` when `i = 0`. This is the indexed-prefix generalization of `foldl`,
and subsumes operations like `prefixSum_specificDuplicate`, `prefixMin_specificDuplicate`, `prefixMax_specificDuplicate`, etc.

`maxPrefixD emptyVal oobVal nums e` computes `max(emptyVal, nums[0], …, nums[e-1])`,
using `getD oobVal` for index access and an explicit empty-prefix value.
This is the `getD`-based, max-specialized alternative to `prefixFold`.

Requires `[Inhabited α]` (for `prefixFold`) / `[Max α]` (for `maxPrefixD`).
-/

namespace List

/-- Cumulative left fold over prefixes of a list, queried at a specific index.
    `prefixFold f xs init i` folds `f` over `init` and `xs[1]!, …, xs[i]!`.
    Returns `init` when `i = 0`. -/
def prefixFold {α : Type} [Inhabited α] (f : α → α → α) (xs : List α) (init : α) : Nat → α
  | 0 => init
  | i'+1 => f (prefixFold f xs init i') (xs[i'+1]!)

/-! ### `maxPrefixD` — prefix maximum with explicit defaults via `getD`

`maxPrefixD emptyVal oobVal nums e` computes `max(emptyVal, nums[0], …, nums[e-1])`,
where out-of-bounds accesses use `oobVal` as a fallback. Returns `emptyVal` when `e = 0`.

Unlike `prefixFold` (which uses `Inhabited α` + `!` and a generic fold function),
this def is specialized to `max` and uses `getD` with explicit defaults. This
generalizes `List.prefixMax_specificDuplicate` (which hardcodes `0` for both defaults) and supports
sentinel-based patterns where the empty prefix has a specific value (e.g., `-1`).

Compare with `List.maxPrefix` in `List/Min.lean`, which uses `Inhabited` + `!`
and treats `maxPrefix a 0` as `a[0]!` (not an explicit sentinel). -/

/-- Prefix maximum with explicit defaults.
    `maxPrefixD emptyVal oobVal nums e` computes `max(emptyVal, nums[0], …, nums[e-1])`,
    where out-of-bounds accesses use `oobVal`. Requires `[Max α]` for `max`. -/
def maxPrefixD {α : Type} [Max α] (emptyVal : α) (oobVal : α) (nums : List α) : Nat → α
  | 0 => emptyVal
  | n + 1 => max (maxPrefixD emptyVal oobVal nums n) ((nums[n]?).getD oobVal)

/-! ### `prefixFoldGetD` — general `getD`-based prefix fold

`prefixFoldGetD f init default xs i` folds `f` over `init` and
`(xs[0]?).getD default`, …, `(xs[i-1]?).getD default`.
Returns `init` when `i = 0`.

This generalizes `maxPrefixD` (which hardcodes `f := max`) by allowing any
binary function `f : α → α → α`.  Use this when you need a prefix fold other than
`max` — for example, `prefixFoldGetD max` recovers `maxPrefixD`, and
`prefixFoldGetD (λ acc x => acc + x)` (with `init := 0`) gives a `getD`-based
prefix sum.

Compare with `prefixFold` (which uses `!` / `Inhabited` instead of `getD`). -/

/-- Cumulative left fold over prefixes using `getD` for safe index access.
`prefixFoldGetD f init default xs i` folds `f` over `init` and
`(xs[0]?).getD default`, …, `(xs[i-1]?).getD default`.
Returns `init` when `i = 0`. -/
def prefixFoldGetD {α : Type} (f : α → α → α) (init : α) (default : α) (xs : List α) : Nat → α
  | 0 => init
  | i+1 => f (prefixFoldGetD f init default xs i) ((xs[i]?).getD default)

/-- `maxPrefixD` is `prefixFoldGetD` with `f := max`. -/
lemma maxPrefixD_eq_prefixFoldGetD {α : Type} [Max α] (emptyVal oobVal : α) (nums : List α) (n : Nat) :
    maxPrefixD emptyVal oobVal nums n = prefixFoldGetD max emptyVal oobVal nums n := by
  induction n with
  | zero => simp [maxPrefixD, prefixFoldGetD]
  | succ n ih => simp [maxPrefixD, prefixFoldGetD, ih]

/-! ### `prefixMaxD` — prefix maximum with single fallback

`prefixMaxD fallback xs i` computes the maximum of `(xs[0]?).getD fallback`,
`(xs[1]?).getD fallback`, …, `(xs[i]?).getD fallback`. Unlike `maxPrefixD`, which
uses a separate empty-prefix sentinel (`emptyVal`) and returns it at index 0,
`prefixMaxD` uses the list's first element (or `fallback` if empty) at index 0.
This is the more direct "maximum over the first i+1 elements" semantics.

Formally: `prefixMaxD fallback xs i = max_{k=0}^{i} (xs[k]?).getD fallback`. -/

/-- Prefix maximum computed over list elements `xs[0]` through `xs[i]`,
using `fallback` for out-of-bounds and for the base case when the list is empty.
`prefixMaxD fallback xs 0 = (xs[0]?).getD fallback`.
`prefixMaxD fallback xs (i+1) = max ((xs[i+1]?).getD fallback) (prefixMaxD fallback xs i)`. -/
def prefixMaxD {α : Type u} [Max α] (fallback : α) (xs : List α) : Nat → α
  | 0 => (xs[0]?).getD fallback
  | i+1 => max ((xs[i+1]?).getD fallback) (prefixMaxD fallback xs i)

/-- Characterization lemma: if a function `f` satisfies the same base case
and recurrence as `prefixMaxD`, then it is equal to `prefixMaxD`.
Useful for proving alternative definitions or folding a specification
into `prefixMaxD` during algorithm verification. -/
lemma prefixMaxD_eq_of_step {α : Type u} [Max α] (fallback : α) (xs : List α) {f : Nat → α}
    (h0 : f 0 = (xs[0]?).getD fallback)
    (hstep : ∀ n, f (n + 1) = max ((xs[n + 1]?).getD fallback) (f n)) :
    ∀ n, f n = prefixMaxD fallback xs n := by
  intro n
  induction n with
  | zero =>
      simpa [prefixMaxD] using h0
  | succ n ih =>
      rw [hstep n, ih]
      simp [prefixMaxD]

end List
