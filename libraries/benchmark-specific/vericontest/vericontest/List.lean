import Mathlib

open List

namespace List

/-- Safe indexed access to a list: returns the element at index `i` if it exists,
otherwise returns `fallback`. Equivalent to `(xs[i]?).getD fallback`. -/
def getWithDefault {α : Type u} (fallback : α) (xs : List α) (i : Nat) : α :=
  (xs[i]?).getD fallback

/-- Safe indexed access to a list using `Inhabited.default` as the fallback value.
This is the `Inhabited`-based convenience wrapper around `getWithDefault`.
Equivalent to `(xs[i]?).getD default`. -/
def getDefault {α : Type u} [Inhabited α] (xs : List α) (i : Nat) : α :=
  getWithDefault default xs i

/-- Get the (i, j)-th element of a list of lists, returning `d` if either index is out of bounds.
This is a two-dimensional generalization of `getWithDefault` for nested list structures.
Equivalent to `(lists[i]?.map (λ row => row[j]?).getD d).getD d`. -/
def nestedGetD {α : Type u} (lists : List (List α)) (i j : Nat) (d : α) : α :=
  match lists[i]? with
  | none => d
  | some row => getWithDefault d row j

/-- Get the (i, j)-th element of a list of lists, using `Inhabited` for the default value.
This is a convenience version of `nestedGetD` that uses the `Inhabited` instance instead of
an explicit default parameter. Returns `default` if either index is out of bounds. -/
def nestedGet {α : Type u} [Inhabited α] (lists : List (List α)) (i j : Nat) : α :=
  nestedGetD lists i j default

/-- Get the (i, j)-th element of a list of lists, returning `Option α`.
Returns `none` if either index is out of bounds.
This is the `Option`-based variant of `nestedGetD` and `nestedGet`,
analogous to how `xs[i]?` is the `Option`-based variant of `xs.getD i d`. -/
def nestedGet? {α : Type u} (lists : List (List α)) (i j : Nat) : Option α :=
  (lists[i]?).bind fun row => row[j]?

/-- Two-dimensional `ofFn` lemma for `nestedGet?`: accessing a matrix built via
`List.ofFn` of `List.ofFn` at valid indices `(p, q)` returns `some (f ⟨p, hp⟩ ⟨q, hq⟩)`.
This bridges `nestedGet?` (the `Option`-based 2D accessor) to the generating function `f`,
and is the `Option` counterpart of `getElem!_ofFn2` (which uses total `getElem!` access). -/
lemma nestedGet?_ofFn_ofFn {α : Type u} {r c : Nat} (f : Fin r → Fin c → α) (p q : Nat) (hp : p < r) (hq : q < c) :
    nestedGet? (List.ofFn (λ i : Fin r => List.ofFn (f i))) p q = some (f ⟨p, hp⟩ ⟨q, hq⟩) := by
  unfold nestedGet?
  simp [List.getElem?_ofFn, hp, hq]

/-- Get the length of the `i`-th inner list in a nested list structure.
Returns `0` if `i` is out of bounds (i.e., `i ≥ lists.length`).
Equivalent to `(lists[i]?.getD []).length`.

This is a convenience function for matrix/2D-array processing where you need
to know the length of a specific row, generalizing the `row_len` pattern from
LeetCode problems (e.g. LC 1582 "Special Positions in a Binary Matrix"). -/
def nestedLength {α : Type u} (lists : List (List α)) (i : Nat) : Nat :=
  ((lists[i]?).getD []).length

/-- Get the `r`-th row of a matrix (list of lists). Returns `[]` if `r` is out of bounds.
Equivalent to `(lists[r]?).getD []`.

This is a convenience wrapper for safe row extraction in matrix/2D-array processing,
generalizing the `row` pattern from LeetCode problems (e.g. LC 1937
"Maximum Number of Points with Cost"). See also `nestedGetD` for single-element access
and `nestedLength` for getting the length of a row. -/
def getRow {α : Type u} (lists : List (List α)) (r : Nat) : List α :=
  getWithDefault [] lists r

/-- Get the (i, j)-th element of a list of lists, where indices are `ℤ` and negative
indices for the outer dimension are guarded (returning `d`). The inner dimension `j`
uses `Int.toNat` truncation (negative `j` → index 0). Equivalent to `get_field`
from LeetCode 1333 generalized from `Int` to any type with a default.
See also `nestedGetD` for the `Nat`-indexed version. -/
def nestedGetDIntTrunc {α : Type u} (lists : List (List α)) (i j : ℤ) (d : α) : α :=
  if i ≥ 0 then
    nestedGetD lists i.toNat j.toNat d
  else
    d

/-- 2D list access (list of lists) with `ℤ` indices using `Int.toNat` truncation.
Returns `0` (via `Zero α`) for out-of-bounds indices. Negative indices are truncated
to `0` by `Int.toNat`, so they access the first row/column rather than being rejected.
This generalizes `grid_get` from LeetCode grid/matrix problems where both dimensions
use `Int` indices and the "zero for out-of-bounds" convention holds.
See also `nestedGetDIntTrunc` which guards the outer dimension against negative indices. -/
def nestedGetInt0 {α : Type u} [Zero α] (lists : List (List α)) (i j : ℤ) : α :=
  nestedGetD lists i.toNat j.toNat 0

/-- Get the length of the `i`-th inner list (row) in a nested list structure, using a `ℤ` index.
Negative indices are truncated to `0` by `Int.toNat`. Returns `0` if the outer index is
out of bounds. This generalizes `row_len_of` from LeetCode grid/matrix problems.
See also `nestedLength` for the `Nat`-indexed version. -/
def nestedLengthZ {α : Type u} (lists : List (List α)) (i : ℤ) : Nat :=
  nestedLength lists i.toNat

/-- When `i` is a valid index (i < lists.length), `nestedLength` returns the length
of the i-th inner list. This bridges the total `nestedLength` accessor (which returns
0 for out-of-bounds indices) to the partial `lists[i]` accessor (which requires the
bound proof `hi`). Generalizes `row_len_eq_length_of_lt` from LeetCode matrix problems. -/
lemma nestedLength_eq_length_of_lt {α : Type u} (lists : List (List α)) (i : Nat) (hi : i < lists.length) :
    nestedLength lists i = (lists[i]).length := by
  simp [nestedLength, List.getElem?_eq_getElem hi]

/-- When a `Fin` index is in bounds on `xs`, `(xs[i.val]?).getD default` is an element of `xs`. -/
lemma getD_mem_of_fin {α : Type u} (xs : List α) (default : α)
    (i : Fin xs.length) : (xs[i.val]?).getD default ∈ xs := by
  rw [getElem?_eq_getElem i.isLt, Option.getD_some]
  exact getElem_mem i.isLt

/-- `getWithDefault` with a `Fin` index that is in bounds returns an element of the list. -/
lemma getWithDefault_mem_of_fin {α : Type u} (xs : List α) (fallback : α)
    (i : Fin xs.length) : xs.getWithDefault fallback i.val ∈ xs := by
  rw [getWithDefault]; exact getD_mem_of_fin _ _ _

/-- If `∀ x ∈ xs, decide (x = a) = false`, then for any in-bounds index `i`, `xs[i] ≠ a`.
This is useful when working with `List.findIdx?` results: if `findIdx?` returns `none`,
then no element in the list equals the target. -/
lemma get_ne_of_forall_decide_eq_false {α : Type u} [DecidableEq α] {xs : List α} {a : α}
    (h : ∀ x ∈ xs, decide (x = a) = false) (i : Nat) (hlt : i < xs.length) : List.get xs ⟨i, hlt⟩ ≠ a := by
  intro heq
  have hx := h (List.get xs ⟨i, hlt⟩) (List.get_mem _ _)
  rw [heq] at hx; simp at hx

/-! ### `allGE` / `allLE` — all elements ≥ / ≤ a threshold

`allGE xs k` asserts that every element of `xs` is ≥ `k`, expressed in `Fin`-indexed
form: `∀ i : Fin xs.length, xs[i] ≥ k`. `allLE` is the dual (all ≤).
These are natural companions to `getD_ge_of_all_ge` / `getD_le_of_all_le`, which
use the membership-based formulation. The `allGE_iff_forall_mem` lemma bridges them.

`allGE` appears in problems like LeetCode 3066 ("Minimum Operations to Make
Elements Within K") where the goal is to make all elements ≥ some threshold. -/

/-- `allGE xs k` asserts that every element of `xs` is ≥ `k`:
`∀ i : Fin xs.length, xs[i] ≥ k`. -/
def allGE {α : Type u} [LE α] (xs : List α) (k : α) : Prop :=
  ∀ i : Fin xs.length, xs[i] ≥ k

/-- `allLE xs k` asserts that every element of `xs` is ≤ `k`:
`∀ i : Fin xs.length, xs[i] ≤ k`. -/
def allLE {α : Type u} [LE α] (xs : List α) (k : α) : Prop :=
  ∀ i : Fin xs.length, xs[i] ≤ k

/-- `allGE xs k` holds iff `∀ x ∈ xs, k ≤ x`.
Bridges the `Fin`-indexed formulation to the membership-based one. -/
lemma allGE_iff_forall_mem {α : Type u} [LE α] {xs : List α} {k : α} :
    allGE xs k ↔ ∀ x ∈ xs, k ≤ x := by
  constructor
  · intro h x hx
    rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (xs.get i) (List.get_mem xs i)

/-- `allLE xs k` holds iff `∀ x ∈ xs, x ≤ k`.
Bridges the `Fin`-indexed formulation to the membership-based one. -/
lemma allLE_iff_forall_mem {α : Type u} [LE α] {xs : List α} {k : α} :
    allLE xs k ↔ ∀ x ∈ xs, x ≤ k := by
  constructor
  · intro h x hx
    rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (xs.get i) (List.get_mem xs i)

/-- If every element of `s` is ≥ `lb`, then `s.getD i d` is also ≥ `lb` when `i` is in bounds.
The default value `d` is irrelevant since `i` is valid. This is a fundamental lemma
connecting `∀ x ∈ s, lb ≤ x` to safe indexed access via `getD`. -/
lemma getD_ge_of_all_ge {α : Type u} [LE α] (s : List α) (i : Nat) (d lb : α)
    (h_all : ∀ x ∈ s, lb ≤ x) (h_bound : i < s.length) : lb ≤ s.getD i d := by
  have h_eq : s.getD i d = s.get ⟨i, h_bound⟩ := by
    simp [h_bound]
  rw [h_eq]
  have h_mem : s.get ⟨i, h_bound⟩ ∈ s := List.get_mem s ⟨i, h_bound⟩
  exact h_all _ h_mem

/-- If every element of `s` is ≤ `ub`, then `s.getD i d` is also ≤ `ub` when `i` is in bounds.
The default value `d` is irrelevant since `i` is valid. This is the dual of `getD_ge_of_all_ge`. -/
lemma getD_le_of_all_le {α : Type u} [LE α] (s : List α) (i : Nat) (d ub : α)
    (h_all : ∀ x ∈ s, x ≤ ub) (h_bound : i < s.length) : s.getD i d ≤ ub := by
  have h_eq : s.getD i d = s.get ⟨i, h_bound⟩ := by
    simp [h_bound]
  rw [h_eq]
  have h_mem : s.get ⟨i, h_bound⟩ ∈ s := List.get_mem s ⟨i, h_bound⟩
  exact h_all _ h_mem

/-- `getWithDefault fallback [] i = fallback` — accessing an empty list always returns
the fallback value, regardless of the index. -/
lemma getWithDefault_nil {α : Type u} (fallback : α) (i : Nat) :
    getWithDefault fallback [] i = fallback := by
  unfold getWithDefault; simp

/-- When the index `i` is in bounds, `getWithDefault` equals `List.get`:
`l.getWithDefault d i = l.get ⟨i, h⟩`. The default value `d` is irrelevant
since the index is valid. -/
lemma getWithDefault_eq_get_of_lt {α : Type u} (l : List α) (d : α) (i : Nat) (h : i < l.length) :
    l.getWithDefault d i = l.get ⟨i, h⟩ := by
  dsimp [getWithDefault]
  simp [h]

/-- When the index `i` is in bounds, `getDefault` equals `l[i]` (via the `'h` notation):
`l.getDefault i = l[i]'h`. This is the `getDefault` variant of `getWithDefault_eq_get_of_lt`. -/
lemma getDefault_eq_getElem_of_lt {α : Type u} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l.getDefault i = l[i]'h := by
  dsimp [getDefault]
  simp [getWithDefault_eq_get_of_lt l default i h]

/-! ### Fin-indexed get for cons lists -/

/-- Bound for shifting a `Fin` index backward by 1 in a cons list, when the index is positive:
if `j : Fin ((x :: xs).length)` and `j.val ≠ 0`, then `j.val - 1 < xs.length`.
This is the bound proof needed to construct a `Fin xs.length` for the tail access. -/
lemma fin_pred_lt_length_cons {α : Type u} (x : α) {xs : List α} (j : Fin ((x :: xs).length))
    (hpos : j.val ≠ 0) : j.val - 1 < xs.length := by
  have h : j.val < xs.length + 1 := by simpa using j.is_lt
  omega

/-- When a `Fin` index into `a :: l` is not zero (i.e., does not point to the head),
the element at that index equals the element at index `i.val - 1` in the tail `l`.
This is the `Fin`-based analog of `List.get_cons_succ`, convenient when the index is
known only up to the constraint `i.val ≠ 0` rather than in `succ` form. -/
lemma get_cons_of_ne_zero {α : Type u} {a : α} {l : List α} (i : Fin ((a :: l).length))
    (hpos : i.val ≠ 0) :
    (a :: l).get i = l.get ⟨i.val - 1, fin_pred_lt_length_cons a i hpos⟩ := by
  match i with
  | ⟨0, hi⟩ => exfalso; exact hpos rfl
  | ⟨n+1, hi⟩ => simp

/-! ### Int-indexed get with default -/

/-- Safe indexed access to a list with a `ℤ` index: returns the element at index `i` if
`0 ≤ i < xs.length`, otherwise returns `a₀`.
Unlike `getD` which uses a `Nat` index and treats negative `i.toNat` as `0`,
this correctly returns `a₀` for negative indices.
This generalizes `list_nth` (CF 266B) to any type with a default value. -/
def getDInt {α : Type u} (xs : List α) (a₀ : α) (i : ℤ) : α :=
  if 0 ≤ i ∧ i < (xs.length : ℤ) then
    xs.getD i.toNat a₀
  else
    a₀

@[simp]
lemma getDInt_of_neg {α : Type u} (xs : List α) (a₀ : α) (i : ℤ) (hi : i < 0) : xs.getDInt a₀ i = a₀ := by
  unfold getDInt; simp [hi]

@[simp]
lemma getDInt_of_ge_length {α : Type u} (xs : List α) (a₀ : α) (i : ℤ) (hi : (xs.length : ℤ) ≤ i) :
    xs.getDInt a₀ i = a₀ := by
  unfold getDInt; simp [hi]

/-- When `0 ≤ i < xs.length`, `getDInt` agrees with `getWithDefault`. -/
lemma getDInt_eq_getWithDefault_of_nonneg_and_lt {α : Type u} (xs : List α) (a₀ : α) (i : ℤ)
    (h0 : 0 ≤ i) (hlt : i < (xs.length : ℤ)) :
    xs.getDInt a₀ i = xs.getWithDefault a₀ i.toNat := by
  unfold getDInt getWithDefault
  simp [h0, hlt]

/-! ### `getDIntTrunc` — ℤ-indexed get via `Int.toNat` truncation

`getDIntTrunc xs a₀ i` returns `xs.getD i.toNat a₀`. Unlike `getDInt`, this does not
bounds-check: negative indices are truncated to `0` via `Int.toNat`, and large indices
rely on `getD`'s default behavior. This is useful when the algorithm guarantees
non-negative indices and the simplest ℤ-indexed accessor suffices. -/

/-- Get element at ℤ index `i` from list, truncating `i` to `Nat` via `Int.toNat`.
For `i < 0`, `Int.toNat i = 0`, so this returns `xs[0]` (or `a₀` if `xs` is empty).
For `i ≥ xs.length`, returns `a₀` (via `getD`'s default behavior).
This is simpler than `getDInt` and is used in competitive-programming solutions
that do not need negative-index safety. -/
def getDIntTrunc {α : Type u} (xs : List α) (a₀ : α) (i : ℤ) : α :=
  xs.getD i.toNat a₀

/-- Accessing index `0` of `x :: xs` via `getDIntTrunc` returns `x`. -/
@[simp]
lemma getDIntTrunc_zero {α : Type u} (x : α) (xs : List α) (a₀ : α) :
    getDIntTrunc (x :: xs) a₀ 0 = x := by
  simp [getDIntTrunc, getD]

/-- When `0 ≤ k`, `getDIntTrunc` at index `k+1` of `x :: xs` shifts to an access on `xs` at index `k`. -/
lemma getDIntTrunc_succ {α : Type u} (x : α) (xs : List α) (a₀ : α) (k : ℤ) (hk : 0 ≤ k) :
    getDIntTrunc (x :: xs) a₀ (k + 1) = getDIntTrunc xs a₀ k := by
  dsimp [getDIntTrunc]
  have h_nat : (k + 1 : ℤ).toNat = (k.toNat : ℕ).succ := by omega
  rw [h_nat]
  simp

/-- Shifted-index lemma for `getDIntTrunc` on a cons: when `i < k`,
`getDIntTrunc (x :: xs) a₀ (k - i) = getDIntTrunc xs a₀ (k - (i + 1))`. -/
lemma getDIntTrunc_cons_sub_of_lt {α : Type u} (x : α) (xs : List α) (a₀ : α) (k i : ℤ) (hlt : i < k) :
    getDIntTrunc (x :: xs) a₀ (k - i) = getDIntTrunc xs a₀ (k - (i + 1)) := by
  have hpos : 0 ≤ k - i - 1 := by omega
  have h_eq : k - i = ((k - i - 1) : ℤ) + 1 := by omega
  rw [h_eq, getDIntTrunc_succ x xs a₀ (k - i - 1) hpos]
  congr 1
  omega

/-! ### `getInt0` — ℤ-indexed get returning `0` for invalid indices

`getInt0 xs i` returns `xs.getD i.toNat 0` for `i ≥ 0`, and `0` for `i < 0`.
Unlike `getDIntTrunc` (which truncates negative indices to index 0 via `Int.toNat`,
potentially returning the first element of a nonempty list), this always returns `0`
for negative indices. Unlike `getDInt`, this does not bounds-check — it relies on
`getD`'s default behavior for large positive indices.

This is used in competitive-programming solutions (LeetCode 3218 and others) where
a ℤ-indexed accessor should return 0 for any out-of-bounds condition. -/

/-- Get element at ℤ index `i` from list, returning `0` for any invalid index.
For `i ≥ 0`, delegates to `xs.getD i.toNat 0`. For `i < 0`, returns `0`. -/
def getInt0 {α : Type u} [Zero α] (xs : List α) (i : ℤ) : α :=
  if i ≥ 0 then xs.getD i.toNat 0 else 0

@[simp]
lemma getInt0_of_neg {α : Type u} [Zero α] (xs : List α) (i : ℤ) (hi : i < 0) : xs.getInt0 i = 0 := by
  unfold getInt0; simp [hi]

@[simp]
lemma getInt0_of_nonneg {α : Type u} [Zero α] (xs : List α) (i : ℤ) (hi : 0 ≤ i) :
    xs.getInt0 i = xs.getD i.toNat 0 := by
  unfold getInt0; simp [hi]

/-- When `0 ≤ i` and `i.toNat < xs.length`, `getInt0` equals the element at index `i`. -/
lemma getInt0_eq_of_nonneg_lt {α : Type u} [Zero α] (xs : List α) (i : ℤ) (h0 : 0 ≤ i) (hlt : i.toNat < xs.length) :
    xs.getInt0 i = xs.get ⟨i.toNat, hlt⟩ := by
  rw [getInt0_of_nonneg xs i h0]
  simp [hlt]

/-- The sum of the first `n` elements of a list. -/
def prefixSum_specificDuplicate {α : Type _} [AddMonoid α] (xs : List α) (n : ℕ) : α :=
  (xs.take n).sum

/-- The prefix sum of zero elements is always `0`. -/
@[simp]
lemma prefixSum_zero {α : Type _} [AddMonoid α] (xs : List α) :
    prefixSum_specificDuplicate xs 0 = 0 := by
  simp [prefixSum_specificDuplicate]

/-- When the prefix length equals the list length, `prefixSum_specificDuplicate` equals the full `sum`. -/
lemma prefixSum_of_length_eq {α : Type _} [AddMonoid α] (xs : List α) :
    prefixSum_specificDuplicate xs xs.length = xs.sum := by
  unfold prefixSum_specificDuplicate; simp

/-- When the prefix length is at least the list length, `prefixSum_specificDuplicate` equals the full `sum`.
This generalizes `prefixSum_of_length_eq` to any `i` where `xs.length ≤ i`. -/
lemma prefixSum_of_length_le {α : Type _} [AddMonoid α] (xs : List α) (i : Nat) (h : xs.length ≤ i) :
    prefixSum_specificDuplicate xs i = xs.sum := by
  have htake : xs.take i = xs := List.take_of_length_le h
  simp [prefixSum_specificDuplicate, htake]

/-- Recursive characterization of `prefixSum_specificDuplicate` on a cons list:
`prefixSum_specificDuplicate (x :: xs) (k+1) = x + prefixSum_specificDuplicate xs k`.
This is the key property for computing prefix sums by structural induction. -/
lemma prefixSum_cons_succ {α : Type _} [AddMonoid α] (x : α) (xs : List α) (k : Nat) :
    prefixSum_specificDuplicate (x :: xs) (k+1) = x + prefixSum_specificDuplicate xs k := by
  simp [prefixSum_specificDuplicate]

/-- Decompose `prefixSum_specificDuplicate` at `i+1` into the prefix at `i` plus the i-th element.
Uses `getD` with default `0` so the identity holds even when `i` is out of bounds:
in that case `getD` returns `0` and the prefix sum has already saturated at the full sum. -/
lemma prefixSum_succ_getD {α : Type _} [AddMonoid α] (xs : List α) (i : Nat) :
    prefixSum_specificDuplicate xs (i + 1) = prefixSum_specificDuplicate xs i + xs.getD i 0 := by
  induction' xs with x xs ih generalizing i
  · simp [prefixSum_specificDuplicate]
  · cases i
    · simp [prefixSum_specificDuplicate]
    · rename_i i
      simp [prefixSum_specificDuplicate]
      have h := ih i
      simp [prefixSum_specificDuplicate] at h
      rw [h, add_assoc]

/-- The sum of elements from index `lo` (inclusive) to `hi` (exclusive) in `xs`.
Equivalent to `((xs.take hi).drop lo).sum`.
For `lo ≥ hi`, returns `0`. -/
def sumSlice {α : Type _} [AddCommMonoid α] (xs : List α) (lo hi : ℕ) : α :=
  ((xs.take hi).drop lo).sum

/-- The sum of a contiguous segment of `xs` of length `len` starting at index `start`.
Equivalent to `((xs.drop start).take len).sum`.
This is the "drop-then-take" view (segment by start + length), contrasted with
`sumSlice` which is "take-then-drop" (range by lo + hi). -/
def segmentSum_specificDuplicate {α : Type _} [AddCommMonoid α] (xs : List α) (start len : ℕ) : α :=
  ((xs.drop start).take len).sum

/-- Sum of a contiguous subrange of `xs` from index `lo` (inclusive) to `hi` (exclusive),
with bounds checking. Returns `0` when the range `[lo, hi)` is not within `[0, xs.length)`.

Unlike `sumSlice` and `segmentSum_specificDuplicate`, this def guards against invalid ranges by returning
`0` for out-of-bounds indices, which is useful for ergonomic `Nat`-indexed algorithms
where the caller may not have a proof of validity at hand.

When `lo < hi` and `hi ≤ xs.length`, this equals `segmentSum_specificDuplicate xs lo (hi - lo)`. -/
def sublistSum {α : Type _} [AddCommMonoid α] (xs : List α) (lo hi : ℕ) : α :=
  if lo < hi ∧ hi ≤ xs.length then
    ((xs.drop lo).take (hi - lo)).sum
  else
    0

/-- When the bounds are valid, `sublistSum` agrees with `segmentSum_specificDuplicate`. -/
lemma sublistSum_eq_segmentSum_of_bounds {α : Type _} [AddCommMonoid α] (xs : List α) (lo hi : ℕ)
    (hlo : lo < hi) (hhi : hi ≤ xs.length) : sublistSum xs lo hi = segmentSum_specificDuplicate xs lo (hi - lo) := by
  unfold sublistSum segmentSum_specificDuplicate; simp [hlo, hhi]

/-! ### Sum of multiple non-overlapping segments

`sumSegments xs len starts` computes the total sum of segments of fixed length `len`
starting at each position in `starts`. This is useful for DP algorithms that select
`k` non-overlapping segments and need to compute the total sum of the chosen segments
(e.g., "max sum of k non-overlapping subarrays"). -/

/-- Sum of non-overlapping segments of fixed length `len` starting at each position in
`starts`: `sumSegments xs len starts = ∑_{s ∈ starts} segmentSum_specificDuplicate xs s len`.
When a start position is out of bounds, `segmentSum_specificDuplicate` returns `0` (drop produces `[]`). -/
def sumSegments {α : Type _} [AddCommMonoid α] (xs : List α) (len : Nat) (starts : List Nat) : α :=
  (starts.map (fun s => segmentSum_specificDuplicate xs s len)).sum

@[simp]
lemma sumSegments_nil {α : Type _} [AddCommMonoid α] (xs : List α) (len : Nat) :
    sumSegments xs len [] = 0 := by
  simp [sumSegments]

@[simp]
lemma sumSegments_cons {α : Type _} [AddCommMonoid α] (xs : List α) (len : Nat) (s : Nat) (ss : List Nat) :
    sumSegments xs len (s :: ss) = segmentSum_specificDuplicate xs s len + sumSegments xs len ss := by
  simp [sumSegments]

/-- `sumSegments` is additive in the starts list. -/
lemma sumSegments_append {α : Type _} [AddCommMonoid α] (xs : List α) (len : Nat) (ss₁ ss₂ : List Nat) :
    sumSegments xs len (ss₁ ++ ss₂) = sumSegments xs len ss₁ + sumSegments xs len ss₂ := by
  simp [sumSegments]

/-! ### 2D list operations (matrix of lists)

These functions treat a `List (List α)` as a matrix and compute sums over
row slices and rectangular subregions. Index access uses `nestedGet`, which
returns `default` for out-of-bounds indices. These generalize the pattern
from matrix block-sum problems (LeetCode 1314). -/

/-- Sum of a contiguous slice_specificDuplicate of column indices `[c1, c2)` in row `r` of a 2D list matrix.
Returns `0` when `c1 ≥ c2`. Uses `nestedGet` for safe index access. -/
def rowSumSlice {α : Type _} [Add α] [Zero α] [Inhabited α]
    (mat : List (List α)) (r c1 c2 : Nat) : α :=
  if c1 ≥ c2 then
    0
  else
    nestedGet mat r c1 + rowSumSlice mat r (c1 + 1) c2
termination_by c2 - c1

/-- Sum of all elements in the rectangular subregion `[r1, r2) × [c1, c2)` of a 2D list matrix.
Each row's contribution is computed by `rowSumSlice`. Returns `0` when `r1 ≥ r2`. -/
def rectSumSlice {α : Type _} [Add α] [Zero α] [Inhabited α]
    (mat : List (List α)) (r1 r2 c1 c2 : Nat) : α :=
  if r1 ≥ r2 then
    0
  else
    rowSumSlice mat r1 c1 c2 + rectSumSlice mat (r1 + 1) r2 c1 c2
termination_by r2 - r1

/-- Sum of a contiguous slice_specificDuplicate of row indices `[r1, r2)` in column `c` of a 2D list matrix.
Returns `0` when `r1 ≥ r2`. Uses `nestedGet` for safe index access.
This is the column-oriented dual of `rowSumSlice`: `colSumSlice mat c r1 r2` sums
`mat[r1..r2-1][c]`, while `rowSumSlice mat r c1 c2` sums `mat[r][c1..c2-1]`.
Generalized from `col_sum` in LeetCode 3070 ("Count Submatrices with Top-Left Element
and Sum Less Than k"). -/
def colSumSlice {α : Type _} [Add α] [Zero α] [Inhabited α]
    (mat : List (List α)) (c r1 r2 : Nat) : α :=
  if r1 ≥ r2 then
    0
  else
    nestedGet mat r1 c + colSumSlice mat c (r1 + 1) r2
termination_by r2 - r1

/-- The maximum of the first `len` elements of a list, using `0` as the default for
out-of-bounds access. Returns `0` if `len = 0`. Works for any `LinearOrder` type
with a `Zero` instance (e.g., `Nat`, `Int`, `ℚ`, `ℝ`).
Generalized from `max_to` pattern appearing across solutions (lc1953 and others). -/
def prefixMax_specificDuplicate {α : Type} [LinearOrder α] [Zero α] (xs : List α) (len : Nat) : α :=
  if len = 0 then
    0
  else if len = 1 then
    (xs[0]?).getD 0
  else
    let m := prefixMax_specificDuplicate xs (len - 1)
    let v := (xs[len - 1]?).getD 0
    max v m
termination_by len

/-- The maximum of the elements of `xs` from index `j` to `n` (exclusive). Returns `0` if `j ≥ n`. -/
def suffixMax_specificDuplicate (xs : List Nat) (j n : Nat) : Nat :=
  if j ≥ n then
    0
  else if j + 1 = n then
    xs[j]!
  else
    let m := suffixMax_specificDuplicate xs (j + 1) n
    let v := xs[j]!
    if v > m then v else m
termination_by n - j

/-- Maximum of `xs[0..i]` (inclusive), computed by index recursion.
`prefixMaxAt xs i = max {xs.getD j 0 | 0 ≤ j ≤ i}`.
Uses `getD` with `0` as fallback for out-of-bounds access.
Unlike `prefixMax_specificDuplicate` (which is length-based), this is index-based:
`prefixMaxAt xs i = prefixMax_specificDuplicate xs (i+1)` when `i+1 ≤ xs.length`. -/
def prefixMaxAt {α : Type} [LinearOrder α] [Zero α] (xs : List α) (i : ℕ) : α :=
  match i with
  | 0 => xs.getD 0 0
  | i'+1 =>
    let prev := prefixMaxAt xs i'
    let cur := xs.getD (i'+1) 0
    if cur > prev then cur else prev

/-- Maximum of `xs[i..]` (from index `i` to the end), computed by index recursion.
`suffixMaxFrom xs i = max {xs.getD j 0 | i ≤ j < xs.length}`.
Uses `getD` with `0` as fallback. When `i` is near the end, returns
`xs.getD (xs.length - 1) 0`.
Unlike `suffixMax_specificDuplicate` (which takes explicit end bound `n`), this uses `xs.length`
as the implicit upper bound. -/
def suffixMaxFrom {α : Type} [LinearOrder α] [Zero α] (xs : List α) (i : ℕ) : α :=
  if xs.length ≤ i + 1 then
    xs.getD (xs.length - 1) 0
  else
    let next := suffixMaxFrom xs (i + 1)
    let cur := xs.getD i 0
    if cur > next then cur else next
termination_by xs.length - i

/-- Minimum of `xs[i..]` (from index `i` to the end), computed by index recursion.
`suffixMinFrom xs i = min {xs.getD j 0 | i ≤ j < xs.length}`.
Uses `getD` with `0` as fallback. When `i` is near the end, returns
`xs.getD (xs.length - 1) 0`.
This is the dual of `suffixMaxFrom`. -/
def suffixMinFrom {α : Type} [LinearOrder α] [Zero α] (xs : List α) (i : ℕ) : α :=
  if xs.length ≤ i + 1 then
    xs.getD (xs.length - 1) 0
  else
    let next := suffixMinFrom xs (i + 1)
    let cur := xs.getD i 0
    if cur < next then cur else next
termination_by xs.length - i

/-- Returns the smallest index `i ≤ p` such that `xs[i]!` is maximal among `xs[0..p]!`.
If `p = 0`, returns `0`. Ties are broken in favor of the smallest index
(i.e., the first occurrence of the maximum). -/
def indexOfMaxInPrefix {α : Type _} [LinearOrder α] [Inhabited α] (xs : List α) (p : Nat) : Nat :=
  if h : p = 0 then 0
  else
    let prev := indexOfMaxInPrefix xs (p - 1)
    if xs[prev]! < xs[p]! then p
    else prev
termination_by p

/-- Returns the smallest index `i ≤ p` such that `xs[i]!` is minimal among `xs[0..p]!`.
If `p = 0`, returns `0`. Ties are broken in favor of the smallest index
(i.e., the first occurrence of the minimum).

This is the dual of `indexOfMaxInPrefix`. Generalizes `min_index_prefix` from
LeetCode 3264 ("Final Array State After K Multiplication Operations"). -/
def indexOfMinInPrefix {α : Type _} [LinearOrder α] [Inhabited α] (xs : List α) (p : Nat) : Nat :=
  if h : p = 0 then 0
  else
    let prev := indexOfMinInPrefix xs (p - 1)
    if xs[p]! < xs[prev]! then p
    else prev
termination_by p

/-- The minimum of the first `len` elements of a list. Returns `0` if `len = 0`. -/
def prefixMin_specificDuplicate (xs : List Nat) (len : Nat) : Nat :=
  if len = 0 then
    0
  else if len = 1 then
    xs[0]!
  else
    let m := prefixMin_specificDuplicate xs (len - 1)
    let v := xs[len - 1]!
    if v < m then v else m
termination_by len

/-- The maximum of the first `stop` elements of a list, given a proof that `stop ≤ xs.length`.
Returns `default` if `stop = 0`. This is a proof-bounded, generalized version of `prefixMax_specificDuplicate`
that works for any linear order type with a default inhabitant. -/
def maxOfPrefix {α : Type _} [LinearOrder α] [Inhabited α] (xs : List α) (stop : Nat) (h : stop ≤ xs.length) : α :=
  if h_stop : stop ≤ 1 then
    if h_stop0 : stop = 0 then
      default
    else
      have h0 : 0 < xs.length := by omega
      xs.get ⟨0, h0⟩
  else
    have h_idx : stop - 1 < xs.length := by omega
    let prev := maxOfPrefix xs (stop - 1) (by omega)
    let cur := xs.get ⟨stop - 1, h_idx⟩
    if prev ≥ cur then prev else cur
termination_by stop
decreasing_by
  omega

/-- The maximum of the elements of `xs` except the one at index `k`. The list has `n` elements. -/
def maxExcluding (xs : List Nat) (n k : Nat) : Nat :=
  if k = 0 then
    suffixMax_specificDuplicate xs 1 n
  else if k = n - 1 then
    prefixMax_specificDuplicate xs (n - 1)
  else
    let a := prefixMax_specificDuplicate xs k
    let b := suffixMax_specificDuplicate xs (k + 1) n
    if a > b then a else b

/-- Maximum of all elements in `l` except the one at index `i`.
Returns `0` for empty or singleton lists (no element to exclude).
Uses a recursive `foldl max` approach that works for any `LinearOrder` type with `Zero`.

* `maxExceptIdx (a :: b :: xs) 0 = xs.foldl max b` — exclude `a`, max of rest
* `maxExceptIdx (x :: xs) (i+1) = max x (maxExceptIdx xs i)` — keep `x`, recurse on tail -/
def maxExceptIdx {α : Type*} [LinearOrder α] [Zero α] : List α → Nat → α
  | _ :: x :: xs, 0 => xs.foldl max x
  | x :: xs, i + 1 => max x (maxExceptIdx xs i)
  | _, _ => 0

/-- `mapFilteredRange n keep f` returns the list `[f i | i < n, keep i]`. -/
def mapFilteredRange {α : Type _} (n : Nat) (keep : Nat → Bool) (f : Nat → α) : List α :=
  ((range n).filter keep).map f

lemma mem_mapFilteredRange_iff {α : Type _} (n : Nat) (keep : Nat → Bool) (f : Nat → α) (x : α) :
    x ∈ mapFilteredRange n keep f ↔ ∃ j, j < n ∧ keep j = true ∧ f j = x := by
  unfold mapFilteredRange
  simp only [mem_map, mem_filter, mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hkeep⟩, rfl⟩
    exact ⟨j, hj, hkeep, rfl⟩
  · rintro ⟨j, hj, hkeep, rfl⟩
    exact ⟨j, ⟨hj, hkeep⟩, rfl⟩

/-- Characterize membership in the image of a filtered range.
`b ∈ ((range n).filter p).map f` iff there exists an index `i < n` such that
`p i = true` and `f i = b`. Combines `mem_map_iff` and `mem_filter_range_iff_specificDuplicate`
into a single `↔` for the common `map ∘ filter ∘ range` pipeline. -/
lemma mem_map_filter_range_iff_specificDuplicate {α : Type u} (f : Nat → α) (p : Nat → Bool) (n : Nat) (b : α) :
    b ∈ List.map f (List.filter p (List.range n)) ↔ ∃ i, i < n ∧ p i = true ∧ f i = b := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi_filter, hi_eq⟩
    rcases List.mem_filter.mp hi_filter with ⟨hi_range, hi_p⟩
    exact ⟨i, List.mem_range.mp hi_range, hi_p, hi_eq⟩
  · intro h
    rcases h with ⟨i, hi_range, hi_p, h_eq⟩
    have hi_filter : i ∈ List.filter p (List.range n) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hi_range, hi_p⟩
    exact List.mem_map.mpr ⟨i, hi_filter, h_eq⟩

/-- Membership in `List.filter p (List.range n)` is equivalent to `i < n ∧ p i = true`.
This is a fundamental lemma for reasoning about filtered ranges, useful in any
algorithm that selects indices satisfying a predicate from `[0, n)`. -/
lemma mem_filter_range_iff_specificDuplicate {p : Nat → Bool} {n i : Nat} :
    i ∈ List.filter p (List.range n) ↔ i < n ∧ p i = true := by
  simp [List.mem_filter, List.mem_range]

/-- Membership in `List.filter (λ x => p x && q x) (List.range n)` is equivalent to
`i < n ∧ p i = true ∧ q i = true`. This is the conjunctive extension of `mem_filter_range_iff_specificDuplicate`
for filtering on two predicates simultaneously. -/
lemma mem_filter_range_and_iff {p q : Nat → Bool} {n i : Nat} :
    i ∈ List.filter (λ x => p x && q x) (List.range n) ↔ i < n ∧ p i = true ∧ q i = true := by
  simp [List.mem_filter, List.mem_range]

/-- If `f : Nat → α` is strictly monotone (`a < b → f a < f b`), then mapping `f` over a
filtered range `filter p (range n)` preserves the pairwise `<` relation. This generalizes
the `intIndicesWhere_pairwise` pattern: the natural numbers in `range n` are pairwise `<`,
`filter` preserves it, and monotonicity lifts it through `map`. -/
lemma pairwise_lt_map_filter_range {α : Type u} [LT α]
    (n : Nat) (p : Nat → Bool) (f : Nat → α) (hf : ∀ {a b : Nat}, a < b → f a < f b) :
    List.Pairwise (· < ·) (List.map f (List.filter p (List.range n))) := by
  apply List.Pairwise.map
  · intro a b hab
    exact hf hab
  · exact List.Pairwise.filter p (List.pairwise_lt_range n)

/-! ### Filter nonempty lemmas -/

/-- If a property `P` holds for all elements of `l`, then it also holds for all elements
of the filtered sublist `l.filter f`. This follows because `l.filter f ⊆ l`:
any element in the filtered list is also in the original list. -/
lemma forall_mem_filter_of_forall_mem {l : List α} {f : α → Bool} {P : α → Prop}
    (h : ∀ x ∈ l, P x) : ∀ x ∈ l.filter f, P x := by
  intro x hx
  exact h x (List.mem_of_mem_filter hx)

/-- If `x` is in `l` and `p x` holds, then the filtered list has length at least 1.
This is useful for proving that filtered lists are nonempty. -/
lemma filter_nonempty_of_mem_and_pred {l : List α} {p : α → Bool} {x : α}
    (hmem : x ∈ l) (hpred : p x = true) : (List.filter p l).length ≥ 1 := by
  have hmem_filter : x ∈ List.filter p l := by
    rw [List.mem_filter]
    exact ⟨hmem, hpred⟩
  have hpos : 0 < (List.filter p l).length := List.length_pos_of_mem hmem_filter
  omega

/-- If `j` is a valid index into the list of elements from `xs` whose `f`-value equals `best`,
then `f` applied to that element equals `best`. This is the key property of filtered lists:
all elements in the filter satisfy the predicate. -/
lemma filter_get_value {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) (best : β) {j : ℕ}
    (hj : j < (xs.filter (fun y => f y = best)).length) :
    f (xs.filter (fun y => f y = best))[j] = best := by
  have hm : (xs.filter (fun y => f y = best))[j] ∈
      xs.filter (fun y => f y = best) := List.getElem_mem hj
  exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- If `i` is a valid index into `l.filter p`, then the predicate `p` holds on the element
at that index: `p ((l.filter p).get i) = true`. This is the general `Bool`-predicate version
of `filter_get_value` (which is specialized to `f y = best` comparisons).
Combines `List.getElem_mem` and `List.of_mem_filter`. -/
lemma getElem_filter {α : Type} (l : List α) (p : α → Bool) (i : Fin (l.filter p).length) :
    p ((l.filter p).get i) = true := by
  have hmem := List.getElem_mem (l := l.filter p) i.isLt
  exact List.of_mem_filter hmem

/-! ### Filter complement lemmas -/

/-- The sum of lengths of `filter p l` and `filter (λ x => !(p x)) l` equals the length of `l`.
This is a fundamental identity: filtering a list by a predicate and its negation partitions
the list's elements, so the lengths add up to the total length. -/
lemma filter_not_lengths_add {α : Type u} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (λ x => !(p x))).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x with
    | true => simp [hx, List.length_cons, ih]; omega
    | false => simp [hx, List.length_cons, ih]; omega

/-! ### `range'` membership lemmas -/

/-- Membership in `List.range' 1 n` is equivalent to `1 ≤ x ∧ x ≤ n`.
This is a simplified version of `List.mem_range'_1` for the common case `start = 1`,
where `x < 1 + n` simplifies to `x ≤ n`. -/
lemma mem_range'_one_n_iff (x n : Nat) : x ∈ List.range' 1 n ↔ 1 ≤ x ∧ x ≤ n := by
  constructor
  · intro h
    rw [List.mem_range'_1] at h
    rcases h with ⟨h1, h2⟩
    exact ⟨h1, by omega⟩
  · intro ⟨hx1, hx2⟩
    rw [List.mem_range'_1]
    exact ⟨hx1, by omega⟩

/-- Membership in `List.filter p (List.range' 1 n)` is equivalent to `1 ≤ x ∧ x ≤ n ∧ p x = true`.
This combines `mem_range'_one_n_iff` with `List.mem_filter`. -/
lemma nat_mem_filter_range'_one_n_iff (n : Nat) (p : Nat → Bool) (x : Nat) :
    x ∈ List.filter p (List.range' 1 n) ↔ (1 ≤ x ∧ x ≤ n ∧ p x = true) := by
  constructor
  · intro h
    rcases List.mem_filter.mp h with ⟨hmem, hpred⟩
    rcases (mem_range'_one_n_iff x n).mp hmem with ⟨hx1, hx2⟩
    exact ⟨hx1, hx2, hpred⟩
  · intro ⟨hx1, hx2, hpred⟩
    have hmem : x ∈ List.range' 1 n := (mem_range'_one_n_iff x n).mpr ⟨hx1, hx2⟩
    rw [List.mem_filter]
    exact ⟨hmem, hpred⟩

/-- `(range n).any (λ i => decide (P i))` is equivalent to `∃ i, i < n ∧ P i`.
This is a convenience lemma that combines `any_eq_true`, `mem_range`, and `decide_eq_true_iff`. -/
lemma any_decide_range_iff_exists {n : Nat} {P : Nat → Prop} [DecidablePred P] :
    (range n).any (λ i => decide (P i)) = true ↔ ∃ i, i < n ∧ P i := by
  simp [any_eq_true, mem_range, decide_eq_true_iff]

/-- `(List.range n).all p = true` iff `p i = true` for all `i < n`.
This bridges `List.all` over a range to a universal quantifier over `ℕ`.
The `Bool`-valued predicate `p : ℕ → Bool` makes this suitable for computational
contexts; for `Prop`-valued predicates, use `decideAll_range_iff` instead. -/
lemma all_range_iff (p : ℕ → Bool) (n : ℕ) : (List.range n).all p = true ↔ ∀ i, i < n → p i = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    apply h
    rw [List.mem_range]
    exact hi
  · intro h x hx
    rw [List.mem_range] at hx
    exact h x hx

/-! ### `decideAll` — `List.all` with `Prop` predicates via `decide`

`decideAll xs p` is `xs.all (λ x => decide (p x))`. It bridges `List.all`
(which takes `α → Bool`) with `Prop`-valued predicates `α → Prop` using `decide`.
This is the universal-quantifier counterpart of the `List.any` + `decide` pattern
used in `any_decide_range_iff_exists`. -/

/-- `decideAll xs p = true` iff `∀ x ∈ xs, p x`. Equivalent to `xs.all (λ x => decide (p x))`.
Bridges `List.all` (Bool-valued) to `Prop`-valued predicates via `decide`. -/
def decideAll {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p] : Bool :=
  xs.all (fun x => decide (p x))

/-- `decideAll` over a list is equivalent to a `∀ x ∈ xs, p x` proposition. -/
lemma decideAll_eq_true_iff {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p] :
    decideAll xs p = true ↔ ∀ x ∈ xs, p x := by
  simp [decideAll]

/-- `decideAll` on `range n` is equivalent to `∀ j < n, p j`.
This is the `Prop`-predicate counterpart of `all_range_iff`. -/
lemma decideAll_range_iff {p : ℕ → Prop} [DecidablePred p] (n : ℕ) :
    decideAll (List.range n) p = true ↔ ∀ j < n, p j := by
  simp [decideAll]

/-- `(List.range n).any p = true` iff `p i = true` for some `i < n`.
This bridges `List.any` over a range to an existential quantifier over `ℕ`.
The `Bool`-valued predicate `p : ℕ → Bool` makes this suitable for computational
contexts; for `Prop`-valued predicates, use `any_decide_range_iff_exists` instead. -/
lemma any_range_iff_specificDuplicate (p : ℕ → Bool) (n : ℕ) : (List.range n).any p = true ↔ ∃ i, i < n ∧ p i = true := by
  rw [List.any_eq_true]
  constructor
  · intro ⟨i, hi, h⟩
    rw [List.mem_range] at hi
    exact ⟨i, hi, h⟩
  · intro ⟨i, hi, h⟩
    exact ⟨i, by rw [List.mem_range]; exact hi, h⟩

/-! ### `existsNatUpTo` — bounded existential on `Nat`

`existsNatUpTo limit p` tests whether `∃ i ≤ limit, p i = true`.
It is defined as `(List.range (limit + 1)).any p` and bridges `List.any`
with the `≤`-based bounded existential quantifier over `Nat`. -/

/-- `existsNatUpTo limit p = true` iff there exists `i ≤ limit` such that `p i = true`. -/
def existsNatUpTo (limit : Nat) (p : Nat → Bool) : Bool :=
  (List.range (limit + 1)).any p

/-- Characterization of `existsNatUpTo` via an existential with `≤`.
This is the `≤` counterpart of `any_range_iff_specificDuplicate` (which uses `<`). -/
lemma existsNatUpTo_eq_true_iff {limit : Nat} {p : Nat → Bool} :
    existsNatUpTo limit p = true ↔ ∃ k, k ≤ limit ∧ p k = true := by
  unfold existsNatUpTo
  rw [any_range_iff_specificDuplicate]
  constructor
  · rintro ⟨k, hk_lt, hk_true⟩
    exact ⟨k, Nat.lt_succ_iff.mp hk_lt, hk_true⟩
  · rintro ⟨k, hk_le, hk_true⟩
    exact ⟨k, Nat.lt_succ_of_le hk_le, hk_true⟩

/-- A variant of `existsNatUpTo_eq_true_iff` that rewrites the predicate via `h`.
Useful when `p` is defined in terms of a `Prop`-valued predicate `q`. -/
lemma existsNatUpTo_eq_true_iff_of {limit : Nat} {p : Nat → Bool} {q : Nat → Prop}
    (hpq : ∀ k, p k = true ↔ q k) :
    existsNatUpTo limit p = true ↔ ∃ k, k ≤ limit ∧ q k := by
  rw [existsNatUpTo_eq_true_iff]
  constructor
  · rintro ⟨k, hk_le, hk_true⟩
    exact ⟨k, hk_le, (hpq k).1 hk_true⟩
  · rintro ⟨k, hk_le, hq⟩
    exact ⟨k, hk_le, (hpq k).2 hq⟩

/-! ### `any₂` — nested `List.any` with dependent second list

`any₂ xs ys p = true` iff `∃ x ∈ xs, ∃ y ∈ ys x, p x y = true`.
This is the nested-existential counterpart of `List.any`, where the second
list `ys` can depend on the element `x` from the first list. Useful for
checking existence of pairs satisfying a relation (e.g., "does there
exist an index p and an index q such that condition C holds?"). -/

/-- Nested `List.any`: `any₂ xs ys p = true` iff `∃ x ∈ xs, ∃ y ∈ ys x, p x y = true`.
The second list `ys x` depends on the element `x` from the first list `xs`. -/
def any₂ {α β : Type*} (xs : List α) (ys : α → List β) (p : α → β → Bool) : Bool :=
  xs.any fun x => (ys x).any (p x)

/-- `any₂ xs ys p = true` iff there exists `x ∈ xs` and `y ∈ ys x` such that `p x y = true`. -/
lemma any₂_eq_true_iff {α β : Type*} (xs : List α) (ys : α → List β) (p : α → β → Bool) :
    any₂ xs ys p = true ↔ ∃ x ∈ xs, ∃ y ∈ ys x, p x y = true := by
  simp [any₂]

/-! ### `ofFnNat` — building a list from a `Nat → α` and a length

`ofFnNat n f` produces the list `[f 0, f 1, …, f (n-1)]`. It is equivalent to
`(List.range n).map f` and wraps `List.ofFn` with a `Nat → α` function instead of a
`Fin n → α` function. This is convenient when the generating function is naturally
defined on `Nat`. -/

/-- Build a list by applying `f : Nat → α` to the first `n` natural numbers:
`ofFnNat n f = [f 0, f 1, …, f (n-1)]`. Equivalent to `(range n).map f`. -/
def ofFnNat {α : Type u} (n : Nat) (f : Nat → α) : List α :=
  List.ofFn (λ (i : Fin n) => f i.val)

lemma ofFnNat_length {α : Type u} (n : Nat) (f : Nat → α) :
    (ofFnNat n f).length = n := by
  simp [ofFnNat]

lemma ofFnNat_get {α : Type u} (n : Nat) (f : Nat → α)
    (i : Fin (ofFnNat n f).length) :
    (ofFnNat n f).get i = f i.val := by
  unfold ofFnNat
  have h := List.get_ofFn (λ (i' : Fin n) => f i'.val) i
  rw [h]
  simp

/-- For a list `L` that equals `List.ofFn` of a function depending only on the index value,
getting an element simplifies to evaluating the function at that index value.
Combines `List.get_ofFn` with `Fin.cast` simplification.

This is useful when `L` is defined as an `ofFn` (or proven equal to one) and you need
to prove a property about `L.get i` in terms of the generating function `f`. -/
lemma get_ofFn_val_dep {n : Nat} {α : Type} {L : List α} (f : Nat → α)
    (hL : L = List.ofFn (fun (j : Fin n) => f j.val))
    (i : Fin L.length) : L.get i = f i.val := by
  subst hL
  rw [List.get_ofFn]
  simp

/-! ### `map_indices` — map a `ℕ → β` over the indices of a list

`map_indices xs f` produces a list `[f 0, f 1, …, f (xs.length - 1)]` — the same
length as `xs`, where each position `i` holds `f i`. This is convenient when the length
is given by an existing list and the values at each position depend only on the index.

It is definitionally equal to `ofFnNat xs.length f`. -/

/-- Build a list of the same length as `xs` where each position `i` holds `f i`:
`map_indices xs f = [f 0, f 1, …, f (xs.length - 1)]`. Equivalent to `ofFnNat xs.length f`. -/
def map_indices (xs : List α) (f : ℕ → β) : List β :=
  List.ofFn (fun (i : Fin xs.length) => f (i.val))

/-- The length of `map_indices xs f` equals `xs.length`. -/
lemma map_indices_length (xs : List α) (f : ℕ → β) : (map_indices xs f).length = xs.length := by
  simp [map_indices]

/-- For an in-bounds index `i`, `(map_indices xs f).get` returns `f i`. -/
lemma map_indices_get (xs : List α) (f : ℕ → β) (i : ℕ) (h : i < (map_indices xs f).length) :
    (map_indices xs f).get ⟨i, h⟩ = f i := by
  unfold map_indices
  have hget := List.get_ofFn (fun (i' : Fin xs.length) => f (i'.val)) ⟨i, h⟩
  simp [hget]

/-! ### `tabulateRec` — building a list by induction on the prefix

`tabulateRec n base next` builds a list of length `n+1` where each entry can depend
on all previously computed entries and the current index. This is the fundamental
pattern behind dynamic-programming table generation: the next value is computed from
the full history of values already built, together with the position index.

For a simpler version that does not need the full prefix history, see `ofFnNat`
which just applies `f i` for each `i < n`. -/

/-- Build a list of length `n+1` by induction on the prefix:
`tabulateRec n base next` produces `[a₀, a₁, …, aₙ]` where

* `a₀ = base`
* `a_{k+1} = next [a₀, …, aₖ] (k+1)` for `k < n`.

The `next` function receives the full list of elements built so far (`prev`) and the
current 1-based index. This is useful for dynamic-programming tables where each entry
depends on all previously computed entries (e.g., game-theory DP, combinatorial tables).

Example: `tabulateRec 3 0 (λ prev i => prev.sum + i)` builds `[0, 1, 3, 7]` since:
`a₀ = 0`, `a₁ = 0 + 1 = 1`, `a₂ = (0+1) + 2 = 3`, `a₃ = (0+1+3) + 3 = 7`. -/
def tabulateRec {α : Type u} (n : Nat) (base_val : α) (next : List α → Nat → α) : List α :=
  match n with
  | 0 => [base_val]
  | n' + 1 =>
    let prev := tabulateRec n' base_val next
    prev ++ [next prev (n' + 1)]
termination_by n

lemma tabulateRec_length {α : Type u} (n : Nat) (base_val : α) (next : List α → Nat → α) :
    (tabulateRec n base_val next).length = n + 1 := by
  induction n with
  | zero => simp [tabulateRec]
  | succ n ih =>
    unfold tabulateRec
    simp [ih]

lemma tabulateRec_zero {α : Type u} (base_val : α) (next : List α → Nat → α) :
    tabulateRec 0 base_val next = [base_val] := by
  simp [tabulateRec]

lemma tabulateRec_succ {α : Type u} (n : Nat) (base_val : α) (next : List α → Nat → α) :
    tabulateRec (n + 1) base_val next =
    (tabulateRec n base_val next) ++ [next (tabulateRec n base_val next) (n + 1)] := by
  simp [tabulateRec]

lemma tabulateRec_head {α : Type u} (n : Nat) (base_val : α) (next : List α → Nat → α) :
    (tabulateRec n base_val next).head? = some base_val := by
  induction n with
  | zero => simp [tabulateRec]
  | succ n ih => simp [tabulateRec_succ, ih]

lemma getElem!_ne_of_lt_of_nodup {α : Type _} [Inhabited α] {xs : List α} (h : xs.Nodup)
    {i k : Nat} (hik : i < k) (hk : k < xs.length) :
    xs[i]! ≠ xs[k]! := by
  have hi : i < xs.length := lt_trans hik hk
  have hgeti : xs[i]! = xs[i] := by
    simp [LawfulGetElem.getElem!_def, getElem?_eq_getElem hi]
  have hgetk : xs[k]! = xs[k] := by
    simp [LawfulGetElem.getElem!_def, getElem?_eq_getElem hk]
  intro heq
  have heq' : xs[i] = xs[k] := by
    rw [← hgeti, ← hgetk]
    exact heq
  exact (Nat.ne_of_lt hik) ((Nodup.getElem_inj_iff h).mp heq')

/-- Sum of list elements from `startIdx` onwards whose index satisfies `selector`.
This is a recursive version of `(xs.drop startIdx).` filtered by a predicate on indices,
but using `List.get` with index-based access. -/
def sumIdxFrom {α : Type _} [AddMonoid α] (xs : List α)
    (selector : ℕ → Prop) [DecidablePred selector] (startIdx : ℕ) : α :=
  if h_lt : startIdx < xs.length then
    (if selector startIdx then xs.get ⟨startIdx, h_lt⟩ else 0) +
    sumIdxFrom xs selector (startIdx + 1)
  else
    0
termination_by xs.length - startIdx
decreasing_by
  omega

/-- Sum of `max(0, target - a[i])` for `i` from `start` to the end of the list.
This computes the total deficit relative to `target` — how much each element
falls short of `target`, summed over all elements from `start` onward. -/
def sumDeficitFrom {α : Type _} [LinearOrderedAddCommGroup α] (a : List α) (start : Nat) (target : α) : α :=
  if h : start < a.length then
    let x := a.get ⟨start, h⟩
    (if target > x then target - x else 0) + sumDeficitFrom a (start + 1) target
  else
    0
termination_by a.length - start
decreasing_by
  omega

/-- Recursively sum `f` applied to symmetric pairs of list `a` (with length `n`).
For each `i` from `0` to `ed-1`, pairs `a[i]` with `a[n-1-i]` and accumulates `f a[i] a[n-1-i]`.
Uses `List.get!` for index access (returns `default` if out-of-bounds). -/
def symPairSum {α : Type _} [Inhabited α] (a : List α) (n : Nat) (f : α → α → Nat) (ed : Nat) : Nat :=
  match ed with
  | 0 => 0
  | ed' + 1 =>
    symPairSum a n f ed' + f (a[ed']!) (a[n - (ed' + 1)]!)
termination_by ed

/-- Sum of `f` applied to all symmetric pairs of list `a` (with length `n`).
Equivalent to `symPairSum a n f (n / 2)`. -/
def symPairTotal {α : Type _} [Inhabited α] (a : List α) (n : Nat) (f : α → α → Nat) : Nat :=
  symPairSum a n f (n / 2)

/-- `SortedLE_specificDuplicate a` asserts that `a` is non-decreasing when accessed via indices:
for all `i ≤ j`, `a[i] ≤ a[j]`.
This is equivalent to `List.Sorted (· ≤ ·) a` and is useful for index-based proofs. -/
def SortedLE_specificDuplicate {α : Type _} [LE α] (a : List α) : Prop :=
  ∀ (i j : Fin a.length), (i : Nat) ≤ (j : Nat) → a[i] ≤ a[j]

/-- In a `SortedLE_specificDuplicate` list with at least two elements, the first element is ≤ the second. -/
lemma SortedLE_specificDuplicate.head_le_second {α : Type _} [LE α] {a b : α} {l : List α}
    (h : SortedLE_specificDuplicate (a :: b :: l)) : a ≤ b := by
  have h01 : ((⟨0, by simp⟩ : Fin (a :: b :: l).length) : Nat) ≤
      ((⟨1, by simp⟩ : Fin (a :: b :: l).length) : Nat) := by
    simp
  simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ h01

/-- The result of `mergeSort` with `(· ≤ ·)` comparator is `SortedLE_specificDuplicate`.
This bridges mathlib's `List.sorted_mergeSort'` to the `SortedLE_specificDuplicate` index-based definition. -/
lemma mergeSort_sortedLE {α : Type _} [LinearOrder α] (l : List α) :
    SortedLE_specificDuplicate (l.mergeSort (· ≤ ·)) := by
  have h_sorted : List.Sorted (· ≤ ·) (l.mergeSort (· ≤ ·)) := by
    simpa using List.sorted_mergeSort' (· ≤ ·) l
  intro i j hij
  have := h_sorted.rel_get_of_le hij
  simpa using this

/-- `mergeSort` preserves `Nodup`: if `l` is nodup, then `l.mergeSort r` is also nodup.
This follows directly from `List.Perm.nodup_iff` and `List.mergeSort_perm`. -/
lemma mergeSort_nodup_of_nodup {α : Type} (r : α → α → Bool) {l : List α} (h : l.Nodup) :
    (l.mergeSort r).Nodup :=
  (List.Perm.nodup_iff (List.mergeSort_perm l r)).mpr h

/-! ### `StrictlySorted` — global strict sortedness via `Fin` indices

`StrictlySorted a` asserts that `a` is strictly increasing when accessed via indices:
for all `i < j`, `a[i] < a[j]`. This is the strict analog of `SortedLE_specificDuplicate` and is
equivalent to `List.Sorted (· < ·) a` for transitively comparable types.

This predicate generalizes `strictly_increasing` from LeetCode 3731 (which used
`List Nat` specifically) to any `LT` type. -/

/-- `StrictlySorted a` asserts that `a` is strictly increasing when accessed via
`Fin` indices: for all `i < j`, `a[i] < a[j]`.
Equivalent to `List.Sorted (· < ·) a` for transitively comparable types. -/
def StrictlySorted {α : Type _} [LT α] (a : List α) : Prop :=
  ∀ (i j : Fin a.length), (i : Nat) < (j : Nat) → a[i] < a[j]

/-- In a `StrictlySorted` list with at least two elements, the first element is < the second. -/
lemma StrictlySorted.head_lt_second {α : Type _} [LT α] {a b : α} {l : List α}
    (h : StrictlySorted (a :: b :: l)) : a < b := by
  have h01 : ((⟨0, by simp⟩ : Fin (a :: b :: l).length) : Nat) <
      ((⟨1, by simp⟩ : Fin (a :: b :: l).length) : Nat) := by
    simp
  simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ h01

/-- If every element of `l` is > `a` and `l` is `StrictlySorted`, then `a :: l` is also
`StrictlySorted`. This is the key lemma for constructing strictly increasing lists
by consing a strictly smaller element at the front. -/
lemma StrictlySorted.cons {α : Type _} [LT α] {a : α} {l : List α}
    (h_lt : ∀ x ∈ l, a < x) (h_si : StrictlySorted l) : StrictlySorted (a :: l) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with (rfl | ⟨i', rfl⟩)
  · rcases Fin.eq_zero_or_eq_succ j with (rfl | ⟨j', rfl⟩)
    · exact absurd hij (Nat.lt_irrefl _)
    · simpa using h_lt (l.get j') (List.get_mem l j')
  · rcases Fin.eq_zero_or_eq_succ j with (rfl | ⟨j', rfl⟩)
    · have h0 : (0 : Fin (l.length + 1)).val = 0 := rfl
      have hsucc : (Fin.succ i').val = i'.val + 1 := rfl
      rw [h0, hsucc] at hij
      exact absurd hij (Nat.not_lt_zero _)
    · have hij' : i'.val < j'.val := by
        have hsucc_i : (Fin.succ i').val = i'.val + 1 := rfl
        have hsucc_j : (Fin.succ j').val = j'.val + 1 := rfl
        rw [hsucc_i, hsucc_j] at hij
        exact Nat.lt_of_succ_lt_succ hij
      have h_lt' : l.get i' < l.get j' := h_si i' j' hij'
      simpa using h_lt'

/-- If `xs` has known length `n` and all elements at distinct indices are distinct
(using `getElem?`), then `xs` is nodup. This is a convenience wrapper around
`List.nodup_iff_getElem?_ne_getElem?` when the length is available as a hypothesis. -/
lemma nodup_of_getElem?_ne_of_length {α : Type u} {xs : List α} {n : Nat}
    (hlen : xs.length = n)
    (huniq : ∀ i j : Nat, i < j → j < n → xs[i]? ≠ xs[j]?) :
    xs.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  exact huniq i j hij (by simpa [hlen] using hj)

/-- If all `getD` values at distinct indices are distinct, then the list is nodup.
This is the `getD`-based formulation of `nodup_of_getElem?_ne_of_length`, convenient when
uniqueness is stated using `getD` (safe indexed access with a default value) rather than
`getElem?`. -/
lemma nodup_of_getD_ne {α : Type u} [DecidableEq α] {d : α} {l : List α}
    (h : ∀ (i j : Nat), i < j → j < l.length → l.getD i d ≠ l.getD j d) : List.Nodup l := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  intro heq
  apply h i j hij hj
  simpa [List.getD] using congrArg (fun o => o.getD d) heq

/-- In a nodup list, if `xs[i]? = some x`, then `idxOf x` returns `i`. -/
lemma idxOf_eq_of_getElem?_eq_some {α : Type u} [DecidableEq α]
    {xs : List α} {i : Nat} {x : α}
    (hnodup : xs.Nodup) (hget : xs[i]? = some x) :
    xs.idxOf x = i := by
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hi, hx⟩
  simpa [hx] using List.idxOf_getElem hnodup i hi

/-- In a nodup list, elements at distinct `Fin` indices with different values are distinct.
This is a `Fin`-based version of `getElem!_ne_of_lt_of_nodup`, using `List.get`
instead of `getElem!`. It follows directly from `List.Nodup.get_inj_iff`. -/
lemma nodup_get_ne_of_lt {α : Type u} (l : List α) (h : l.Nodup) (i j : Fin l.length) (hij : i.val < j.val) :
    l.get i ≠ l.get j := by
  intro heq
  have h_eq_fin : i = j := (List.Nodup.get_inj_iff h).mp heq
  have h_val_eq : i.val = j.val := by simpa using congrArg Fin.val h_eq_fin
  omega

/-! ### getElem! ↔ getElem bridge -/

/-- When the index is in bounds, `getElem!` equals `getElem`:
`l[i]! = l[i]` whenever `i < l.length`. This is a fundamental lemma bridging
total and partial list access. -/
lemma getElem!_eq_getElem_of_lt_specificDuplicate {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l[i]! = l[i] := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- When the index is in bounds, `getElem` equals `getElem!`:
`l[i] = l[i]!` whenever `i < l.length`.
This is the symmetric version of `getElem!_eq_getElem_of_lt_specificDuplicate`. -/
lemma getElem_eq_getElem!_of_lt {α : Type _} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l[i] = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

/-- When the index is in bounds, `getElem!` distributes over `List.map`:
`(l.map f)[i]! = f l[i]!`. This is the `getElem!` counterpart of `List.getElem_map`. -/
lemma getElem!_map_eq {α β : Type _} [Inhabited α] [Inhabited β]
    (f : α → β) (l : List α) {i : Nat} (hi : i < l.length) :
    (l.map f)[i]! = f l[i]! := by
  have himap : i < (l.map f).length := by simpa using hi
  rw [getElem!_pos (l.map f) i himap, getElem!_pos l i hi]
  exact List.getElem_map f

/-- When `i < n`, `(List.ofFn f)[i]! = f ⟨i, h⟩` — accessing `List.ofFn f` at a valid
index via `getElem!` returns the function value at the corresponding `Fin` index.
This is the `getElem!` counterpart of `List.getElem?_ofFn`. -/
lemma getElem!_ofFn {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → α) (i : ℕ) (h : i < n) :
    (List.ofFn f)[i]! = f ⟨i, h⟩ := by
  have hget? : (List.ofFn f)[i]? = some (f ⟨i, h⟩) := by
    rw [List.getElem?_ofFn]
    simp [h]
  have hget! : (List.ofFn f)[i]! = ((List.ofFn f)[i]?).getD default := by
    simp
  rw [hget!, hget?]
  simp

/-- Two-dimensional version of `getElem!_ofFn`: for a matrix built via nested `List.ofFn`,
accessing at valid indices `(i, j)` via `getElem!` returns `f ⟨i, hi⟩ ⟨j, hj⟩`.
This is useful for matrix operations where both dimensions use `List.ofFn` construction. -/
lemma getElem!_ofFn2 {m n : ℕ} {α : Type} [Inhabited α] {f : Fin m → Fin n → α}
    {i j : ℕ} (hi : i < m) (hj : j < n) :
    ((List.ofFn (λ (i' : Fin m) => List.ofFn (λ (j' : Fin n) => f i' j')))[i]!)[j]! = f ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [getElem!_ofFn (λ (i' : Fin m) => List.ofFn (λ (j' : Fin n) => f i' j')) i hi]
  rw [getElem!_ofFn (f ⟨i, hi⟩) j hj]

/-- Accessing `(range n).map f` at index `i < n` gives `some (f i)`. -/
lemma getElem?_map_range_specificDuplicate {α : Type u} (f : Nat → α) {n i : Nat}
    (hi : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  simp [List.getElem?_map, List.getElem?_range hi]

/-- Accessing `(range n).map f` at index `i < n` directly gives `f i`.
This is the `getElem` (non-Option) version of `getElem?_map_range_specificDuplicate`.
Generalized from `tabulate_getElem` which used `(range (n+1)).map f`. -/
lemma getElem_map_range_specificDuplicate {α : Type u} (f : Nat → α) {n i : Nat} (h : i < n) :
    ((List.range n).map f)[i]'(by simpa using h) = f i := by
  have hlen : i < (List.range n).length := by simpa using h
  calc
    ((List.range n).map f)[i]'(by simpa using h) = f ((List.range n)[i]'hlen) := by simp
    _ = f i := by simp [List.getElem_range i hlen]

/-- If a boolean function `f` corresponds to a proposition `P` (i.e., `f a = true ↔ P a`
for all `a`), then `(map f xs)[i]? = some true` iff `P` holds for `xs[i]`.
This bridges `Bool`-valued list processing (e.g., `List.map isPrimeBool nums`) with
propositional specifications (`is_prime`). -/
lemma getElem?_map_eq_some_true_iff {α : Type} (xs : List α) (f : α → Bool) (P : α → Prop) (i : Nat)
    (hcorr : ∀ a, f a = true ↔ P a) (hi : i < xs.length) :
    ((List.map f xs)[i]? = some true ↔ P (xs[i])) := by
  simp [List.getElem?_map, List.getElem?_eq_some_iff, hi, hcorr (xs[i])]

/-! ### getElem! to mem conversion -/

/-- If a property `P` holds for all elements accessed via `getElem!` (i.e., for every index
in bounds), then `P` holds for every element of the list.
This is a convenience lemma bridging `getElem!`-based reasoning to membership-based reasoning,
combining `forall_getElem` and `getElem!_pos`. -/
lemma forall_mem_of_forall_getElem! {α : Type _} [Inhabited α] (xs : List α) (P : α → Prop)
    (h : ∀ i, i < xs.length → P xs[i]!) : ∀ x ∈ xs, P x :=
  (forall_getElem.1 (fun i hi => by
    simpa [getElem!_pos xs i hi] using h i hi))

/-! ### Adjacent pair predicates -/

/-- Check that a binary boolean predicate `p` holds for all adjacent pairs in a list.
Returns `true` for empty and singleton lists (vacuously).
For example, `allAdjacentPairs_specificDuplicate (· < ·) [1, 3, 5] = true`. -/
def allAdjacentPairs_specificDuplicate {α : Type _} (p : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => p a b && allAdjacentPairs_specificDuplicate p (b :: t)

/-- `allAdjacentPairs_specificDuplicate p nums = true` iff for every adjacent pair at indices `i` and `i+1`
in `nums`, `p nums[i] nums[i+1] = true`. Uses `getElem!` for total access.
This bridges the structural recursion definition to an index-based formulation
useful for proofs involving `Fin` index ranges. -/
lemma allAdjacentPairs_iff_specificDuplicate {α : Type _} [Inhabited α] (p : α → α → Bool) (nums : List α) :
    allAdjacentPairs_specificDuplicate p nums = true ↔ ∀ i : Fin (nums.length - 1), p (nums[i.1]!) (nums[i.1+1]!) = true := by
  induction nums with
  | nil => simp [allAdjacentPairs_specificDuplicate]
  | cons a xs ih =>
    cases xs with
    | nil => simp [allAdjacentPairs_specificDuplicate]
    | cons b xs =>
      simp only [allAdjacentPairs_specificDuplicate, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hab, ht⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using hab
        | succ i =>
          simpa using ht ⟨i, by simp only [List.length_cons] at *; omega⟩
      · intro h
        constructor
        · simpa using h ⟨0, by simp⟩
        · intro i
          simpa using h ⟨i.val + 1, by have := i.isLt; simp only [List.length_cons] at *; omega⟩

/-- Check whether elements at index `i` and `i+1` are equal in `xs`,
provided both indices are in bounds. Returns `false` if either index is out of bounds.

This is an index-based predicate useful for position-indexed reasoning about adjacent
elements (e.g., in array-like algorithms). For list-based reasoning, prefer
`countAdjacentEqual` which uses pattern matching.

Generalizes both `adjEqAt` and `adjacent_pair_equal` from CF 266A ("Stones on the Table"). -/
def adjacentEqualAt {α : Type} [BEq α] (xs : List α) (i : Nat) : Bool :=
  i + 1 < xs.length && (xs[i]? == xs[i + 1]?)

/-- Count the number of adjacent equal pairs in a list.
Returns `0` for empty and singleton lists (vacuous).
For `a :: b :: t`, adds `1` if `a == b` and recurses on `b :: t`.

This pattern appears in CF 266A ("Stones on the Table"), where the minimum number
of stones to remove equals the count of adjacent stones with the same color.

Example: `countAdjacentEqual [1, 1, 2, 3, 3] = 2`. -/
def countAdjacentEqual {α : Type} [BEq α] : List α → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a == b then 1 else 0) + countAdjacentEqual (b :: t)

/-- `countAdjacentEqual (xs ++ [x, x]) = countAdjacentEqual (xs ++ [x]) + 1`:
appending a duplicate element increases the adjacent-equal count by 1.
The last two appended elements form a new equal pair, while the original tail was
already counted. -/
lemma countAdjacentEqual_append_dup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (x : α) :
    countAdjacentEqual (xs ++ [x, x]) = countAdjacentEqual (xs ++ [x]) + 1 := by
  induction xs with
  | nil => simp [countAdjacentEqual]
  | cons a xs ih =>
    cases xs with
    | nil => simp [countAdjacentEqual]
    | cons b xs =>
      simpa only [List.cons_append, countAdjacentEqual, Nat.add_assoc] using
        congrArg (fun n => (if a == b then 1 else 0) + n) ih

/-- `countAdjacentEqual` never exceeds `length - 1` for nonempty lists. -/
lemma countAdjacentEqual_le_length_sub_one {α : Type} [BEq α] (xs : List α) (h : xs ≠ []) :
    countAdjacentEqual xs ≤ xs.length - 1 := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => simp [countAdjacentEqual]
    | cons b xs =>
      have hb := ih (by simp)
      simp only [countAdjacentEqual, List.length_cons] at *
      split <;> omega

/-! ### Count consecutive triplets satisfying a predicate

`countTriplets nums p k` counts how many consecutive triplets (at indices i, i+1, i+2
for i < k) in `nums` satisfy the ternary predicate `p`. This is a sliding-window pattern
common in LeetCode problems (e.g., LC 3392, LC 2367) for counting subarrays/substrings
of fixed length matching a criterion.

The `Inhabited α` constraint is needed for the `!` (total get) operator; when indices
are out of bounds, `default` is returned and the predicate may or may not hold. The
caller is expected to ensure `k+2 ≤ nums.length` to avoid degenerate cases. -/

/-- Count how many consecutive triplets (at indices i, i+1, i+2 for i < k)
in `nums` satisfy the predicate `p`. -/
def countTriplets {α : Type} [Inhabited α] (nums : List α) (p : α → α → α → Prop) [∀ a b c, Decidable (p a b c)] (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k'+1 =>
    countTriplets nums p k' + (if p (nums[k']!) (nums[k'+1]!) (nums[k'+2]!) then 1 else 0)

@[simp]
lemma countTriplets_zero {α : Type} [Inhabited α] (nums : List α) (p : α → α → α → Prop) [∀ a b c, Decidable (p a b c)] :
    countTriplets nums p 0 = 0 := rfl

lemma countTriplets_succ {α : Type} [Inhabited α] (nums : List α) (p : α → α → α → Prop) [∀ a b c, Decidable (p a b c)] (k : Nat) :
    countTriplets nums p (k+1) =
    countTriplets nums p k + (if p (nums[k]!) (nums[k+1]!) (nums[k+2]!) then 1 else 0) := rfl

/-! ### Adjacent pair sums

`adjacentPairSums nums` computes the list of sums of each adjacent pair in `nums`.
For `[a, b, c, d]` it returns `[a+b, b+c, c+d]`. Works for any type with `Add`. -/

/-- Compute sums of all adjacent pairs (length-2 subarrays) in the list.
Works for any type with addition. -/
def adjacentPairSums {α : Type} [Add α] (nums : List α) : List α :=
  match nums with
  | a :: b :: rest => (a + b) :: adjacentPairSums (b :: rest)
  | _ => []

/-- If `i + 1 < nums.length`, then `i` is a valid index into `adjacentPairSums nums`.
Equivalently, the adjacent-pair-sums list has at most one fewer element than the original. -/
lemma lt_adjacentPairSums_length {α : Type} [Add α] (nums : List α) (i : ℕ) (h : i + 1 < nums.length) :
    i < (adjacentPairSums nums).length := by
  induction' nums with a as ih generalizing i
  · exact absurd h (by simp)
  · cases as with
    | nil =>
      have : i + 1 < 1 := by simpa using h
      omega
    | cons b bs =>
      simp [adjacentPairSums]
      have hlen : (a :: b :: bs).length = bs.length + 2 := by simp
      rw [hlen] at h
      by_cases hi : i = 0
      · subst hi; omega
      · have hi_sub_bound : i - 1 + 1 < (b :: bs).length := by
          simp
          omega
        have ih_result := ih (i - 1) hi_sub_bound
        omega

/-- Sum `f` over consecutive gaps: `sumOverGaps f l prev = f(l₀-prev) + f(l₁-l₀) + ...`.
Generalizes `total_cost_from` from CF 1921C and similar gap-cost summation patterns. -/
def sumOverGaps {α β : Type _} [Sub α] [AddCommMonoid β] (f : α → β) : List α → α → β
  | [], _ => 0
  | x :: xs, prev => f (x - prev) + sumOverGaps f xs x

/-! ### Maximum adjacent difference in a prefix -/

/-- Maximum adjacent difference in the first `k` elements of a list.
For each `i < k`, computes `a[i+1] - a[i]` (using `fallback` for out-of-bounds access),
and returns the maximum of these differences. Returns `0` for `k = 0`.

Useful for finding the largest gap in a sorted sequence of values, e.g.,
gas station positions where the answer depends on the maximum interval between
consecutive stations. -/
def maxAdjacentDiffPrefix {α : Type u} [LinearOrderedAddCommGroup α] (fallback : α) (a : List α) (k : Nat) : α :=
  match k with
  | 0 => 0
  | k'+1 =>
    let gap := ((a[k'+1]?).getD fallback) - ((a[k']?).getD fallback)
    max (maxAdjacentDiffPrefix fallback a k') gap

/-- Maximum adjacent difference in a list, computed via structural recursion.
Returns `0` for empty and singleton lists (vacuous).
For `a :: b :: t`, computes `max (b - a) (maxAdjacentDiff (b :: t))`.

Unlike `maxAdjacentDiffPrefix`, which uses index-based access with a fallback value
and works on a prefix of the list, this version uses structural pattern matching on
the whole list. It is simpler and does not require a fallback value.

This is useful when computing the maximum gap between consecutive elements in a
sorted list (e.g., LeetCode 1637 "Widest Vertical Area"). -/
def maxAdjacentDiff {α : Type u} [AddGroup α] [LinearOrder α] : List α → α
  | [] | [_] => 0
  | a :: tl@(b :: _) => max (b - a) (maxAdjacentDiff tl)

/-! ### Positive adjacent gaps (sum of positive rises) -/

/-- `posAdjacentGap xs i = max 0 (xs[i+1] - xs[i])`, with out-of-bounds returning `0`.
This is the positive difference from `xs[i]` to `xs[i+1]` — i.e., the amount by which
the next element exceeds the current one. Returns `0` if the difference is non-positive
or if either index is out of bounds. -/
def posAdjacentGap {α : Type u} [LinearOrderedAddCommGroup α] (xs : List α) (i : Nat) : α :=
  max 0 (xs.getD (i + 1) 0 - xs.getD i 0)

/-- Prefix sum of positive adjacent gaps: `∑_{i=0}^{k-1} posAdjacentGap xs i`.
Equivalently, `∑_{i=0}^{k-1} max(0, xs[i+1] - xs[i])`.
This computes the total "positive rise" across the first `k` adjacent pairs.
`prefixSumPosGaps xs 0 = 0` and each step adds the positive gap at index `k`. -/
def prefixSumPosGaps {α : Type u} [LinearOrderedAddCommGroup α] (xs : List α) : Nat → α
  | 0 => 0
  | k + 1 => prefixSumPosGaps xs k + posAdjacentGap xs k

/-- `posAdjacentGap xs i` is always nonnegative. -/
lemma posAdjacentGap_nonneg {α : Type u} [LinearOrderedAddCommGroup α] (xs : List α) (i : Nat) :
    0 ≤ posAdjacentGap xs i := by
  unfold posAdjacentGap; exact le_max_left _ _

/-! ### Sortedness from adjacent comparisons -/

/-- The result of `mergeSort` with a decidable total order (given as a `Prop`-relation
with transitivity and totality) is sorted by that relation.
Unlike mathlib's `List.sorted_mergeSort` which takes `Bool`-valued arguments, this version
accepts `r_trans : r a b → r b c → r a c` and `r_total : r a b ∨ r b a` as `Prop` hypotheses,
yielding `List.Sorted r` as a `Prop`. -/
lemma mergeSort_sorted_rel {α : Type _} (r : α → α → Prop) [DecidableRel r]
    (r_trans : ∀ {a b c : α}, r a b → r b c → r a c)
    (r_total : ∀ a b : α, r a b ∨ r b a)
    (l : List α) : List.Sorted r (l.mergeSort (fun x y => decide (r x y))) := by
  letI : IsTotal α r := ⟨r_total⟩
  letI : IsTrans α r := ⟨fun _ _ _ hab hbc => r_trans hab hbc⟩
  exact List.sorted_mergeSort' r l

/-- If every adjacent pair in `l` satisfies `≤`, then `l` is sorted (non-decreasing).
This is the "local-to-global" principle for sortedness: it suffices to check
that each element is `≤` its immediate successor. -/
theorem sorted_of_adjacent_le [LinearOrder α] [Inhabited α] (l : List α)
    (h : ∀ i, i+1 < l.length → l[i]! ≤ l[i+1]!) : Sorted (· ≤ ·) l := by
  -- First, prove that adjacent ≤ extends to arbitrary i < j via transitivity
  have le_chain : ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]! := by
    intro i j hlt_ij hj
    induction j generalizing i
    next =>
      exact absurd hlt_ij (Nat.not_lt_zero _)
    next =>
      rename_i n IH
      have hn : n < l.length := Nat.lt_trans (Nat.lt_succ_self n) hj
      by_cases h_eq : i = n
      · rw [h_eq]; exact h n hj
      · have h_lt : i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt_ij) h_eq
        have hle1 : l[i]! ≤ l[n]! := IH i h_lt hn
        have hle2 : l[n]! ≤ l[n+1]! := h n hj
        exact le_trans hle1 hle2
  apply (pairwise_iff_get (R := (· ≤ ·))).mpr
  intro a b hlt
  have ha_val : (a : ℕ) < l.length := a.2
  have hb_val : (b : ℕ) < l.length := b.2
  have h_lt_nat : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hlt
  have h_le_get : l[(a : ℕ)]! ≤ l[(b : ℕ)]! := le_chain (a : ℕ) (b : ℕ) h_lt_nat hb_val
  simpa [getElem!_pos l (a : ℕ) ha_val, getElem!_pos l (b : ℕ) hb_val] using h_le_get

/-! ### Prefix sortedness (adjacent pairs)

`SortedPrefixLE a n` is an index-based predicate that holds when the first `n`
elements of `a` are non-decreasing: for every adjacent pair `a[i]` and `a[i+1]`
with `i+1 < n`, we have `a[i] ≤ a[i+1]`. It also requires `n ≤ a.length` so that
all referenced indices are in bounds.

Unlike `SortedLE_specificDuplicate`, which is a global sortedness property over all `Fin` indices,
`SortedPrefixLE` works on a prefix of the list and only checks adjacent pairs.
This makes it convenient for algorithms that build up sortedness incrementally
or only require the first `n` elements to be sorted. -/

/-- `SortedPrefixLE a n` asserts that the first `n` elements of `a` are non-decreasing
when checked via adjacent pairs. Formally: `n ≤ a.length` and for all `i` with `i+1 < n`,
`(a[i]?).getD 0 ≤ (a[i+1]?).getD 0`. The fallback `0` is used for out-of-bounds access
but is irrelevant since `i+1 < n ≤ a.length` ensures both indices are in bounds. -/
def SortedPrefixLE {α : Type u} [LinearOrder α] [Zero α] (a : List α) (n : Nat) : Prop :=
  n ≤ a.length ∧ ∀ i, i + 1 < n → a.getWithDefault 0 i ≤ a.getWithDefault 0 (i + 1)

/-! ### Segment (range-based) monotonicity

`nondecreasingOn seq lo hi` asserts that for all adjacent pairs within the index
interval `[lo, hi)`, `seq[i]! ≤ seq[i+1]!`. When `lo > hi`, the condition is vacuously
true. Generalizes `non_decreasing` (CF 279C) from `List Int` with `Int` indices to
any `Inhabited` `LE` type with `Nat` indices. -/

/-- `nondecreasingOn seq lo hi` asserts that `seq` is non-decreasing on the index
interval `[lo, hi)`: for every index `i` with `lo ≤ i < hi`, `seq[i]! ≤ seq[i+1]!`.
When `lo > hi`, the condition is vacuously true. -/
def nondecreasingOn {α : Type _} [Inhabited α] [LE α] (seq : List α) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i ∧ i < hi → seq[i]! ≤ seq[i + 1]!

/-- `nonincreasingOn seq lo hi` asserts that `seq` is non-increasing on the index
interval `[lo, hi)`: for every index `i` with `lo ≤ i < hi`, `seq[i]! ≥ seq[i+1]!`.
When `lo > hi`, the condition is vacuously true. -/
def nonincreasingOn {α : Type _} [Inhabited α] [LE α] (seq : List α) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i ∧ i < hi → seq[i]! ≥ seq[i + 1]!

/-! ### foldl min lemmas -/

/-- `foldl min init l` is at most `init`.
This is the inductive invariant for computing the minimum of a list via `foldl`. -/
lemma foldl_min_le_initial_specificDuplicate {α} [LinearOrder α] (l : List α) (init : α) : l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp [List.foldl]
    have h := ih (min init x)
    apply le_trans h
    exact min_le_left _ _

/-- If `x ∈ l`, then `foldl min init l ≤ x`.
Together with `foldl_min_le_initial_specificDuplicate`, this characterizes `foldl min` as a lower bound
for all elements of `l` and the initial value. -/
lemma foldl_min_le_of_mem_specificDuplicate {α} [LinearOrder α] {l : List α} {x : α} (hx : x ∈ l) (init : α) :
    l.foldl min init ≤ x := by
  revert init
  induction l with
  | nil =>
    intro init; exact absurd hx (by simp)
  | cons head tail ih =>
    intro init
    rw [List.mem_cons] at hx
    cases hx with
    | inl h_eq =>
      rw [h_eq]
      simp [List.foldl]
      apply le_trans (foldl_min_le_initial_specificDuplicate tail (min init head))
      exact min_le_right _ _
    | inr hx' =>
      simp [List.foldl]
      exact ih hx' (min init head)

/-- Compute the minimum element of a list using `foldl min`.
Returns `default` for empty list.
For `x :: xs`, equivalent to `xs.foldl min x`. -/
def foldlMin {α} [LinearOrder α] [Inhabited α] (l : List α) : α :=
  match l with
  | [] => default
  | x :: xs => xs.foldl min x

/-- If `x ∈ l`, then `foldlMin l ≤ x`.
This is the key correctness property: `foldlMin` is a lower bound for all elements. -/
lemma foldlMin_le_of_mem {α} [LinearOrder α] [Inhabited α] {l : List α} {x : α} (h : x ∈ l) :
    foldlMin l ≤ x := by
  cases' l with head tail
  · exact absurd h (by simp)
  · rw [foldlMin]
    simp [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      rw [h_eq]
      exact foldl_min_le_initial_specificDuplicate tail head
    | inr h' =>
      exact foldl_min_le_of_mem_specificDuplicate h' head

/-- The result of `foldl min acc xs` is either the initial value `acc` or an element of `xs`.
This is the `min` counterpart of `foldl_max_mem_cons`. -/
lemma foldl_min_mem_specificDuplicate {α} [LinearOrder α] (acc : α) (xs : List α) :
    ∃ z, (z = acc ∨ z ∈ xs) ∧ xs.foldl min acc = z := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, Or.inl rfl, rfl⟩
  | cons y ys ih =>
    simp only [List.foldl]
    by_cases h : acc ≤ y
    · rw [min_eq_left h]
      obtain ⟨z, hz, hzval⟩ := ih acc
      refine ⟨z, ?_, hzval⟩
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (by simp [hz])
    · have hy : y ≤ acc := le_of_not_ge h
      rw [min_eq_right hy]
      obtain ⟨z, hz, hzval⟩ := ih y
      refine ⟨z, ?_, hzval⟩
      rcases hz with rfl | hz
      · exact Or.inr (by simp)
      · exact Or.inr (by simp [hz])

/-- For a nonempty list `xs`, `foldlMin xs` equals some element of `xs`.
This is the "minimum is attained" property. -/
lemma foldlMin_mem {α} [LinearOrder α] [Inhabited α] {xs : List α} (hxs : xs ≠ []) :
    ∃ x ∈ xs, foldlMin xs = x := by
  cases xs with
  | nil => contradiction
  | cons x xs' =>
    rw [foldlMin]
    obtain ⟨z, hz, hzval⟩ := foldl_min_mem_specificDuplicate x xs'
    refine ⟨z, ?_, hzval⟩
    rcases hz with rfl | hz
    · simp
    · simp [hz]

/-- For a nonempty list `xs`, the minimum of `xs.map f` is attained at `f x` for some `x ∈ xs`.
This is the "minimum after mapping is attained" property. -/
lemma foldlMin_map_mem {α β} [LinearOrder β] [Inhabited β] {xs : List α} (f : α → β)
    (hxs : xs ≠ []) : ∃ x ∈ xs, foldlMin (xs.map f) = f x := by
  obtain ⟨y, hy, hmin⟩ := foldlMin_mem (xs := xs.map f) (by simpa using hxs)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact ⟨x, hx, hmin⟩

/-! ### foldl max lemmas -/

/-- `init ≤ foldl max init l`.
This is the inductive invariant for computing the maximum of a list via `foldl`. -/
lemma le_foldl_max_initial {α} [LinearOrder α] (l : List α) (init : α) : init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp [List.foldl]
    have h := ih (max init x)
    apply le_trans ?_ h
    exact le_max_left _ _

/-- If `x ∈ l`, then `x ≤ foldl max init l`.
Together with `le_foldl_max_initial`, this characterizes `foldl max` as an upper bound
for all elements of `l` and the initial value. -/
lemma le_foldl_max_of_mem {α} [LinearOrder α] {l : List α} {x : α} (hx : x ∈ l) (init : α) :
    x ≤ l.foldl max init := by
  revert init
  induction l with
  | nil =>
    intro init; exact absurd hx (by simp)
  | cons head tail ih =>
    intro init
    rw [List.mem_cons] at hx
    cases hx with
    | inl h_eq =>
      rw [h_eq]
      simp [List.foldl]
      apply le_trans ?_ (le_foldl_max_initial tail (max init head))
      exact le_max_right _ _
    | inr hx' =>
      simp [List.foldl]
      exact ih hx' (max init head)

/-- The result of folding `max` over `l` with initial value `init` is an element of `init :: l`. -/
lemma foldl_max_mem_cons {α} [LinearOrder α] (init : α) (l : List α) :
    l.foldl max init ∈ init :: l := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
      simp only [foldl_cons]
      have h := ih (init := max init y)
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · rcases le_total init y with hiy | hyi
        · right; left; simpa [max_eq_right hiy] using h
        · left; simpa [max_eq_left hyi] using h
      · right; right; exact h

/-- The result of `foldl max` with initial value `x` over `xs` is either `x` or an element of `xs`.
This is a corollary of `foldl_max_mem_cons` in disjunctive form, convenient for case analysis. -/
lemma foldl_max_eq_or_mem_specificDuplicate {α} [LinearOrder α] (x : α) (xs : List α) :
    List.foldl max x xs = x ∨ List.foldl max x xs ∈ xs := by
  have hmem := foldl_max_mem_cons x xs
  rcases List.mem_cons.mp hmem with (h | h)
  · left; exact h
  · right; exact h

/-- The result of folding `min` over `l` with initial value `init` is an element of `init :: l`.
This is the `min` counterpart of `foldl_max_mem_cons`. -/
lemma foldl_min_mem_cons {α} [LinearOrder α] (init : α) (l : List α) :
    l.foldl min init ∈ init :: l := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
      simp only [foldl_cons]
      have h := ih (init := min init y)
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · rcases le_total init y with hiy | hyi
        · left; simpa [min_eq_left hiy] using h
        · right; left; simpa [min_eq_right hyi] using h
      · right; right; exact h

/-- `foldl max` is monotone in the initial value:
if `a ≤ b`, then `l.foldl max a ≤ l.foldl max b`. -/
lemma foldl_max_mono_specificDuplicate {α} [LinearOrder α] {a b : α} (h : a ≤ b) (l : List α) :
    l.foldl max a ≤ l.foldl max b := by
  induction' l with hd tl ih generalizing a b
  · exact h
  · rw [List.foldl, List.foldl]
    apply ih
    exact max_le_max h (le_refl hd)

/-- Every element of `init :: l` is ≤ `l.foldl max init`.
This combines `le_foldl_max_initial` and `le_foldl_max_of_mem` into a single lemma
covering both the initial value and all list elements. -/
lemma le_foldl_max_of_mem_cons {α} [LinearOrder α] (init : α) {l : List α} {z : α}
    (hz : z ∈ init :: l) : z ≤ l.foldl max init := by
  cases' (List.mem_cons.mp hz : z = init ∨ z ∈ l) with h_eq h_mem
  · rw [h_eq]; exact le_foldl_max_initial l init
  · exact le_foldl_max_of_mem h_mem init

/-- Compute the maximum element of a list using `foldl max`.
Returns `default` for empty list.
For `x :: xs`, equivalent to `xs.foldl max x`. -/
def foldlMax {α} [LinearOrder α] [Inhabited α] (l : List α) : α :=
  match l with
  | [] => default
  | x :: xs => xs.foldl max x

/-- If `x ∈ l`, then `x ≤ foldlMax l`.
This is the key correctness property: `foldlMax` is an upper bound for all elements. -/
lemma le_foldlMax_of_mem {α} [LinearOrder α] [Inhabited α] {l : List α} {x : α} (h : x ∈ l) :
    x ≤ foldlMax l := by
  cases' l with head tail
  · exact absurd h (by simp)
  · rw [foldlMax]
    simp [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      rw [h_eq]
      exact le_foldl_max_initial tail head
    | inr h' =>
      exact le_foldl_max_of_mem h' head

/-- For a nonempty list, `foldlMax l` is an element of `l`.
This is the "maximum is attained" property. -/
lemma foldlMax_mem {α} [LinearOrder α] [Inhabited α] {l : List α} (hne : l ≠ []) :
    foldlMax l ∈ l := by
  cases' l with hd tl
  · exact absurd rfl hne
  · rw [foldlMax]
    have hmem := foldl_max_mem_cons hd tl
    rcases List.mem_cons.mp hmem with (h | h)
    · rw [h]; exact List.mem_cons_self hd tl
    · exact List.mem_cons_of_mem hd h

/-- `x ≥ foldlMax l` iff `x ≥ a` for every `a ∈ l` (when `l` is nonempty).
This characterizes `x` being an upper bound for all elements of `l`. -/
lemma ge_foldlMax_iff_forall_ge {α} [LinearOrder α] [Inhabited α] {l : List α} {x : α} (hne : l ≠ []) :
    x ≥ foldlMax l ↔ ∀ a ∈ l, x ≥ a := by
  constructor
  · intro hx a ha
    have hle : a ≤ foldlMax l := le_foldlMax_of_mem ha
    exact le_trans hle hx
  · intro h
    have hmax_mem : foldlMax l ∈ l := foldlMax_mem hne
    exact h (foldlMax l) hmax_mem

/-! ### foldl max with a mapping function

These lemmas generalize the `foldl max` family to work with a mapping function `f : α → β`.
Instead of folding `max` over the elements of `xs : List α` directly, we fold
`fun best x => max best (f x)` over `xs`, which computes the maximum of `f x` over `x ∈ xs`
(starting from an initial value). This is captured by `maximum_fold xs f init`.

When `f = id`, these reduce to the existing `foldl max` lemmas. -/

/-- Fold `max` over `xs` after applying `f` to each element:
`maximum_fold xs f init = foldl (fun best x => max best (f x)) init xs`.
This generalizes `foldlMax` to work with a mapping function `f : α → β`. -/
def maximum_fold {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) (init : β) : β :=
  xs.foldl (fun best x => max best (f x)) init

/-- The initial value is ≤ the result of folding `max` over mapped elements.
`init ≤ xs.foldl (fun best y => max best (f y)) init`. -/
lemma foldl_max_ge_init_specificDuplicate {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) (init : β) :
    init ≤ xs.foldl (fun best y => max best (f y)) init := by
  induction xs generalizing init with
  | nil => exact le_rfl
  | cons y ys ih =>
      simp only [List.foldl]
      exact le_trans (le_max_left _ _) (ih (max init (f y)))

/-- If `x ∈ xs`, then `f x ≤ xs.foldl (fun best y => max best (f y)) init`.
All mapped elements are ≤ the result of the fold. -/
lemma foldl_max_ge {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) :
    ∀ (init : β) (x : α), x ∈ xs → f x ≤ xs.foldl (fun best y => max best (f y)) init := by
  induction xs with
  | nil =>
      intro init x hx
      simp at hx
  | cons y ys ih =>
      intro init x hx
      simp only [List.mem_cons] at hx
      simp only [List.foldl]
      cases hx with
      | inl h =>
          subst x
          exact le_trans (le_max_right init (f y))
            (foldl_max_ge_init_specificDuplicate ys f (max init (f y)))
      | inr h =>
          exact ih (max init (f y)) x h

/-- The result of folding `max` over mapped elements can be expressed as the function
value of some element that is either in the list or equal to the function input.
More precisely: if `init = f x`, then there exists `y` such that `(y ∈ xs ∨ y = x)`
and `xs.foldl (fun best z => max best (f z)) init = f y`. -/
lemma foldl_max_mem_specificDuplicate {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) :
    ∀ (init : β) (x : α), init = f x →
      ∃ y, (y ∈ xs ∨ y = x) ∧
        xs.foldl (fun best z => max best (f z)) init = f y := by
  intro init x hinit
  induction xs generalizing init x with
  | nil =>
      exact ⟨x, Or.inr rfl, hinit⟩
  | cons y ys ih =>
      simp only [List.foldl]
      by_cases h : init ≤ f y
      · have hy : max init (f y) = f y := max_eq_right h
        obtain ⟨z, hz, hzval⟩ := ih (f y) y rfl
        refine ⟨z, ?_, ?_⟩
        · rcases hz with hz | rfl
          · apply Or.inl
            simpa only [List.mem_cons]
              using (show z = y ∨ z ∈ ys from Or.inr hz)
          · exact Or.inl (by simp)
        · rw [hy]
          exact hzval
      · have hy : f y ≤ init := le_of_not_ge h
        have hm : max init (f y) = init := max_eq_left hy
        obtain ⟨z, hz, hzval⟩ := ih init x hinit
        have hz' : z ∈ y :: ys ∨ z = x := hz.elim
          (fun hz => Or.inl (by
            simpa only [List.mem_cons]
              using (show z = y ∨ z ∈ ys from Or.inr hz)))
          (fun hz => Or.inr hz)
        exact ⟨z, hz', by
          rw [hm]
          exact hzval⟩

/-- `f x ≤ maximum_fold xs f init` whenever `x ∈ xs`.
This is the key correctness property: the fold is an upper bound for all mapped values. -/
lemma maximum_fold_ge {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) (init : β) {x : α} (hx : x ∈ xs) :
    f x ≤ maximum_fold xs f init := by
  unfold maximum_fold
  exact foldl_max_ge xs f init x hx

/-- If `x ∈ xs`, then there exists `y ∈ xs` such that `maximum_fold xs f (f x) = f y`.
The maximum of the mapped values (starting the fold from `f x`) is attained by
some element in the list. -/
lemma maximum_fold_mem_of_mem {α β : Type} [LinearOrder β]
    (xs : List α) (f : α → β) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ xs, maximum_fold xs f (f x) = f y := by
  obtain ⟨y, hy, hval⟩ := foldl_max_mem_specificDuplicate xs f (f x) x rfl
  refine ⟨y, ?_, ?_⟩
  · rcases hy with hy | rfl
    · exact hy
    · exact hx
  · simpa [maximum_fold] using hval

/-! ### lemmas about `take` and `map`

These lemmas simplify combinations of `List.take` with other list operations
(`foldl`, `map`) that appear when reasoning about prefix computations. -/

/-- Decompose a `foldl` over `l.take (k+1)` into the fold over `l.take k` followed
by applying `f` with `l[k]`. This is useful for proofs about prefix folds, especially
when `foldl` corresponds to a cumulative computation indexed by list positions. -/
lemma foldl_take_succ {α β : Type} (f : β → α → β) (init : β) (l : List α) (k : ℕ) (hk : k < l.length) :
    (l.take (k+1)).foldl f init = f ((l.take k).foldl f init) (l[k]) := by
  have h_take_succ : l.take (k+1) = (l.take k) ++ [l[k]] := List.take_succ_eq_append_getElem hk
  rw [h_take_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Mapping `f` over `l.take l.length` is equivalent to mapping `f` over `l`,
since `l.take l.length = l`. This trivial identity is useful when a computation
produces `(l.take n).map f` and the caller knows `n = l.length`. -/
lemma map_take_length {α β : Type} (l : List α) (f : α → β) : (l.take l.length).map f = l.map f := by
  rw [List.take_length]

/-- When `i < l.length`, the length of `l.take (i+1)` equals `i+1`.
This follows from `List.length_take` and is useful for prefix-length calculations
when the index is known to be within bounds. -/
lemma length_take_of_lt {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.take (i+1)).length = i+1 := by
  rw [List.length_take]
  exact Nat.min_eq_left (Nat.succ_le_of_lt hi)

/-! ### lemmas about `drop` and `take`

These lemmas describe properties of the `drop`-then-`take` pattern common in
sliding-window or subarray algorithms: `(xs.drop start).take len` extracts a
contiguous segment of `xs`. -/

/-- When `s + k ≤ arr.length`, the length of `(arr.drop s).take k` is exactly `k`.
This is a fundamental property used in sliding-window correctness proofs. -/
lemma length_drop_take {α : Type} (arr : List α) (s k : Nat) (h_bound : s + k ≤ arr.length) :
    ((arr.drop s).take k).length = k := by
  rw [List.length_take, List.length_drop]
  omega

/-- Every element of `(arr.drop s).take k` is also an element of `arr` at some index
`s + i`. This is the membership lemma for the `drop`-`take` segment extraction pattern. -/
lemma mem_drop_take {α : Type} (arr : List α) (s k i : Nat) (hi : i < ((arr.drop s).take k).length) :
    ∃ (j : Nat) (hj : j < arr.length), ((arr.drop s).take k).get ⟨i, hi⟩ = arr.get ⟨j, hj⟩ := by
  have hi_drop : i < (arr.drop s).length := by
    have h_take_len : ((arr.drop s).take k).length ≤ (arr.drop s).length := by
      simp
    omega
  have hi_arr : s + i < arr.length := by
    have : (arr.drop s).length = arr.length - s := List.length_drop s arr
    omega
  refine ⟨s + i, hi_arr, ?_⟩
  calc
    ((arr.drop s).take k).get ⟨i, hi⟩ = ((arr.drop s).take k)[i] := rfl
    _ = (arr.drop s)[i] := by simpa using List.getElem_take (arr.drop s) k (h := hi)
    _ = arr[s + i] := by simpa using List.getElem_drop arr s (h := hi_drop)
    _ = arr.get ⟨s + i, hi_arr⟩ := rfl

/-! ### foldl xor -/

/-- Fold XOR over a list of Nat, starting from `0`.
For a nonempty list `x :: xs`, this is `0 ^^^ x ^^^ ...` which equals `x ^^^ ...`
since `0 ^^^ n = n`. This is the XOR counterpart of `foldlMin`/`foldlMax`.
Commonly used in prefix-XOR and range-XOR queries. -/
def foldlXor (l : List Nat) : Nat :=
  l.foldl (· ^^^ ·) 0

@[simp]
lemma foldlXor_nil : foldlXor [] = 0 := rfl

@[simp]
lemma foldlXor_singleton (x : Nat) : foldlXor [x] = x := by
  simp [foldlXor]

/-- General lemma: folding XOR with a function `f : α → Nat` starting from `a` equals
`a ^^^` the fold starting from `0`. This is the key identity for shifting the initial
accumulator in XOR folds. Specializes the identity-function case used in `foldlXor_append`. -/
lemma foldl_xor_eq_xor_foldl_specificDuplicate (f : α → Nat) (a : Nat) (xs : List α) :
    List.foldl (fun acc x => acc ^^^ f x) a xs = a ^^^ (List.foldl (fun acc x => acc ^^^ f x) 0 xs) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    have h0 : (0 : Nat) ^^^ f x = f x := by simp
    rw [h0]
    rw [ih (a ^^^ f x), ih (f x)]
    exact Nat.xor_assoc a (f x) _

/-- Cons case for folding XOR with a function from `0`: the head's function value is XOR-ed
with the fold over the tail. This is the recurrence that `foldl_xor_eq_xor_foldl_specificDuplicate` simplifies
for the `0`-initial case. -/
lemma foldl_xor_cons (g : α → Nat) (x : α) (xs : List α) :
    List.foldl (fun acc x => acc ^^^ g x) 0 (x :: xs) = g x ^^^ (List.foldl (fun acc x => acc ^^^ g x) 0 xs) := by
  simp only [List.foldl]
  have h0 : (0 : Nat) ^^^ g x = g x := by simp
  rw [h0]
  exact foldl_xor_eq_xor_foldl_specificDuplicate g (g x) xs

/-- For the identity function, `foldl (· ^^^ ·) a xs = a ^^^ foldlXor xs`.
This is the specialization of `foldl_xor_eq_xor_foldl_specificDuplicate` to `f = id`, extracted as a standalone
lemma (previously was an inline `h_init` inside `foldlXor_append`). -/
lemma foldlXor_foldl_eq_xor_foldlXor (a : Nat) (l : List Nat) :
    l.foldl (· ^^^ ·) a = a ^^^ foldlXor l := by
  simpa [foldlXor] using foldl_xor_eq_xor_foldl_specificDuplicate id a l

/-- Cons recurrence for `foldlXor`: `foldlXor (x :: xs) = x ^^^ foldlXor xs`.
This is the most convenient form for reasoning about `foldlXor` on non-empty lists. -/
@[simp]
lemma foldlXor_cons (x : Nat) (xs : List Nat) : foldlXor (x :: xs) = x ^^^ foldlXor xs := by
  simp [foldlXor]
  exact foldlXor_foldl_eq_xor_foldlXor x xs

lemma foldlXor_append (l₁ l₂ : List Nat) : foldlXor (l₁ ++ l₂) = foldlXor l₁ ^^^ foldlXor l₂ := by
  calc
    foldlXor (l₁ ++ l₂) = (l₁ ++ l₂).foldl (· ^^^ ·) 0 := rfl
    _ = l₂.foldl (· ^^^ ·) (l₁.foldl (· ^^^ ·) 0) := by rw [List.foldl_append]
    _ = (l₁.foldl (· ^^^ ·) 0) ^^^ foldlXor l₂ := by rw [foldlXor_foldl_eq_xor_foldlXor]
    _ = foldlXor l₁ ^^^ foldlXor l₂ := by rfl

/-- Compute the XOR of list elements from index `start` to `end_` (exclusive).
Returns `0` when `start ≥ end_`. Otherwise recurses from `end_` downward,
XOR-ing `arr.getD (end_-1) 0` into the accumulated result.
This enables efficient range-XOR queries for prefix-XOR-based algorithms. -/
def xorRange (arr : List Nat) (start end_ : Nat) : Nat :=
  if start ≥ end_ then
    0
  else
    xorRange arr start (end_ - 1) ^^^ arr.getD (end_ - 1) 0
termination_by end_ - start
decreasing_by
  omega

@[simp]
lemma xorRange_ge (arr : List Nat) (start end_ : Nat) (h : start ≥ end_) : xorRange arr start end_ = 0 := by
  rw [xorRange]
  rw [if_pos h]

lemma xorRange_lt (arr : List Nat) (start end_ : Nat) (h : start < end_) :
    xorRange arr start end_ = xorRange arr start (end_ - 1) ^^^ arr.getD (end_ - 1) 0 := by
  have hge : ¬ (start ≥ end_) := by omega
  conv =>
    lhs
    rw [xorRange]
  rw [if_neg hge]

/-- XOR all values `f i` for `i` from `0` to `n-1` (exclusive).
`xor_fold_range f n = f 0 ^^^ f 1 ^^^ ... ^^^ f (n-1)`.
Returns `0` when `n = 0`, since `0` is the identity for XOR.
This is the XOR analog of `Nat.prefixSum_specificDuplicate`, using `List.range n` and `foldl`.
Common in competitive programming for range-XOR and prefix-XOR computations
(e.g., LeetCode 1486 "XOR Operation in an Array"). -/
def xor_fold_range (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ^^^ f i) 0

@[simp] lemma xor_fold_range_zero (f : Nat → Nat) : xor_fold_range f 0 = 0 := by
  simp [xor_fold_range]

lemma xor_fold_range_succ (f : Nat → Nat) (n : Nat) :
    xor_fold_range f (n+1) = (xor_fold_range f n) ^^^ f n := by
  simp [xor_fold_range, List.range_succ, List.foldl_append, List.foldl]

/-- Prefix XOR: `prefixXor xs n` computes the XOR of the first `n` elements of `xs`.
`prefixXor xs 0 = 0`, and each step XORs `xs[n-1]` into the accumulated result:
`prefixXor xs (n+1) = prefixXor xs n ^^^ xs.getD n 0`.
This is the XOR analog of `prefixSum_specificDuplicate`; commonly used in range-XOR queries
and prefix-XOR-based algorithms (e.g., LeetCode 1829 "Maximum XOR for Each Query"). -/
def prefixXor (xs : List Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (prefixXor xs n) ^^^ xs.getD n 0

/-! ### `findIdxOf` — forward index search returning `Nat`

`findIdxOf nums target` returns the index of the first occurrence of `target` in `nums`,
or `0` if `target` is not found in `nums`. Note that `0` is also a valid index — this
function is intended for use when `target` is known to be in the list (the caller is
expected to have a proof of membership). For a safer API that returns `Option Nat`,
use `List.findIdx?` from the standard library. For the standard `Bool`-predicate
variant, use `List.findIdx`.

Unlike `List.idxOf` (which returns `length` when not found), this function returns `0`
as the sentinel, which is convenient when the result is used in arithmetic expressions
involving subtraction (e.g., when the largest possible result is needed as a `Nat`). -/

/-- Find the index of the first occurrence of `target` in `nums`, returning `Nat`.
Returns `0` if `target` is not in the list. -/
def findIdxOf {α : Type} [DecidableEq α] (nums : List α) (target : α) : Nat :=
  match nums with
  | [] => 0
  | x :: xs =>
    if x = target then 0
    else 1 + findIdxOf xs target

/-! ### Index search with `Int`/`-1` sentinel -/

/-- Find the first index `i < n` where `a[i]? = some target` (using `d` as default for
out-of-bounds access), returning `i` as `Int`, or `-1` if no such index exists.

Example: `findFirstIdx_specificDuplicate [0,2,1,3] 1 0 4 = 2` -/
def findFirstIdx_specificDuplicate {α : Type u} [DecidableEq α] (a : List α) (target d : α) : Nat → Int
  | 0 => -1
  | k+1 =>
    let r := findFirstIdx_specificDuplicate a target d k
    if r ≠ -1 then
      r
    else if (a[k]?).getD d = target then
      (k : Int)
    else
      -1

/-- Find the last index `i < n` where `a[i]? = some target` (using `d` as default for
out-of-bounds access), returning `i` as `Int`, or `-1` if no such index exists.

Example: `findLastIdx_specificDuplicate [0,2,1,3] 1 0 4 = 2` -/
def findLastIdx_specificDuplicate {α : Type u} [DecidableEq α] (a : List α) (target d : α) : Nat → Int
  | 0 => -1
  | k+1 =>
    if (a[k]?).getD d = target then
      (k : Int)
    else
      findLastIdx_specificDuplicate a target d k

@[simp] lemma findFirstIdx_zero {α : Type u} [DecidableEq α] (a : List α) (target d : α) :
    findFirstIdx_specificDuplicate a target d 0 = -1 := by rfl

lemma findFirstIdx_succ {α : Type u} [DecidableEq α] (a : List α) (target d : α) (k : Nat) :
    findFirstIdx_specificDuplicate a target d (k + 1) =
    (let r := findFirstIdx_specificDuplicate a target d k
    if r ≠ -1 then r
    else if (a[k]?).getD d = target then (k : Int) else -1) := by rfl

@[simp] lemma findLastIdx_zero {α : Type u} [DecidableEq α] (a : List α) (target d : α) :
    findLastIdx_specificDuplicate a target d 0 = -1 := by rfl

lemma findLastIdx_succ {α : Type u} [DecidableEq α] (a : List α) (target d : α) (k : Nat) :
    findLastIdx_specificDuplicate a target d (k + 1) =
    (if (a[k]?).getD d = target then (k : Int) else findLastIdx_specificDuplicate a target d k) := by rfl

/-! ### Counting elements by predicate -/

/-- Count how many elements in the list satisfy predicate `p`, returning an `ℤ` count.
This is a predicate version of `List.count` that works with boolean predicates rather than
decidable equality, and returns `ℤ` for convenience in integer arithmetic.
See `List.countP` in mathlib for the same function returning `Nat`. -/
def countPz {α : Type _} (p : α → Bool) : List α → ℤ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countPz p xs

/-- Singleton lemma for `countPz`. -/
@[simp]
lemma countPz_singleton {α : Type _} (p : α → Bool) (x : α) :
    countPz p [x] = (if p x then 1 else 0) := by
  simp [countPz]

/-- `countPz p xs` is bounded above by the length of the list.
This is a fundamental bound on counting predicates: you cannot count more
elements than the list contains. -/
lemma countPz_le_length {α : Type _} (p : α → Bool) (xs : List α) :
    countPz p xs ≤ (xs.length : ℤ) := by
  induction' xs with x xs ih
  · simp [countPz]
  · simp [countPz, List.length_cons]
    split <;> omega

/-- `countPz p xs` is always nonnegative.
Each element contributes either `0` or `1`, so the sum is never negative. -/
lemma countPz_nonneg {α : Type _} (p : α → Bool) (xs : List α) : 0 ≤ countPz p xs := by
  induction' xs with x xs ih
  · simp [countPz]
  · simp [countPz]
    split <;> omega

/-- Integer-cast version of `List.countP_le_length`:
`(l.countP p : ℤ) ≤ (l.length : ℤ)`.
This bridges mathlib's `Nat`-valued `countP` to `ℤ` inequalities, useful when
the surrounding arithmetic is in `ℤ`. See `countPz_le_length` for the
`ℤ`-valued `countPz` analog. -/
lemma countP_le_length_int {α : Type} (l : List α) (p : α → Bool) : (l.countP p : ℤ) ≤ (l.length : ℤ) := by
  exact mod_cast List.countP_le_length (l := l) (p := p)

/-! ### Counting elements equal to a target (ℤ-valued)

`countz lst x` counts how many times `x` appears in `lst`, returning an `ℤ`.
This is the `ℤ`-valued analog of `List.count` (which returns `Nat`), and the
equality-based counterpart of `countPz` (which counts by an arbitrary predicate).

It is useful in competitive-programming solutions where occurrence counts feed
directly into `ℤ` arithmetic (e.g., balance computations, prefix-sweep algorithms)
and avoids explicit `Nat.cast` conversions. -/

/-- Count occurrences of `x` in `lst`, returning an `ℤ`. General over any decidable equality type.
This is the `ℤ`-valued analog of `List.count`. -/
def countz {α : Type _} [DecidableEq α] (lst : List α) (x : α) : ℤ :=
  match lst with
  | [] => 0
  | h :: t => (if h = x then 1 else 0) + countz t x

/-- `countz` on a singleton list. -/
@[simp]
lemma countz_singleton {α : Type _} [DecidableEq α] (x y : α) :
    countz [x] y = (if x = y then 1 else 0) := by
  simp [countz]

/-- `countz lst x` is bounded above by the length of the list. -/
lemma countz_le_length {α : Type _} [DecidableEq α] (lst : List α) (x : α) :
    countz lst x ≤ (lst.length : ℤ) := by
  induction' lst with h t ih
  · simp [countz]
  · simp [countz, List.length_cons]
    split <;> omega

/-- `countz` relates to `List.count` via `Nat.cast`. -/
lemma countz_eq_natCast_count {α : Type _} [DecidableEq α] (lst : List α) (x : α) :
    countz lst x = (List.count x lst : ℤ) := by
  induction' lst with h t ih
  · simp [countz]
  · simp [countz, List.count_cons, ih]
    split <;> omega

/-- Count how many elements in the list are ≥ `x`, returning an `ℤ` count.
This is a convenience specialization of `countPz` for the `(· ≥ x)` comparison.
Useful for counting elements at or above a threshold (e.g., in special-array problems). -/
def countGeq : List Int → Int → Int
  | [], _ => 0
  | h :: t, x => (if h ≥ x then 1 else 0) + countGeq t x

/-! ### Counting elements equal to a target in a range -/

/-- Count elements equal to `target` in the index range `[lo, hi)` of list `a`.
Uses `d` as the default value for out-of-bounds access.

Example: `countEqInRange [1,0,2,0,3] 0 0 0 5 = 2` -/
def countEqInRange {α : Type u} [DecidableEq α] (a : List α) (target d : α) (lo hi : Nat) : Nat :=
  if h : hi ≤ lo then
    0
  else
    let prev := countEqInRange a target d lo (hi - 1)
    if (a[hi - 1]?).getD d = target then prev + 1 else prev
termination_by hi
decreasing_by
  omega

/-- Count how many elements equal `target` in the prefix `xs[0..upto)` (exclusive),
using `fallback` for out-of-bounds access. Returns `Int`.
This is a simpler alternative to `countEqInRange` when counting from index 0
and the result is needed as an integer.

Example: `countGetDUpto 0 [1,2,1,3] 3 1` (counting 1s in first 3 elements) = `2` -/
def countGetDUpto {α : Type u} [DecidableEq α] (fallback : α) (xs : List α)
    (upto : Nat) (target : α) : Int :=
  match upto with
  | 0 => 0
  | n + 1 =>
    (if (xs[n]?).getD fallback = target then 1 else 0) +
      countGetDUpto fallback xs n target

/-- Recurrence lemma: `countGetDUpto` at `n+1` decomposes into the count at `n`
plus a conditional contribution from the element at index `n`.
This is the counterpart of `cnt_occs_succ` for `countGetDUpto`. -/
lemma countGetDUpto_succ_getD {α : Type u} [DecidableEq α] (fallback : α) (xs : List α) (n : Nat) (target : α) :
    countGetDUpto fallback xs (n + 1) target =
    countGetDUpto fallback xs n target + (if xs.getD n fallback = target then 1 else 0) := by
  simp [countGetDUpto, List.getD, add_comm]

/-- `countGetDUpto fallback xs upto target` is always nonnegative.
Each prefix element contributes either `0` or `1`, so the sum is never negative. -/
lemma countGetDUpto_nonneg {α : Type u} [DecidableEq α] (fallback : α) (xs : List α) (upto : Nat) (target : α) :
    0 ≤ countGetDUpto fallback xs upto target := by
  induction upto with
  | zero => unfold countGetDUpto; omega
  | succ n ih =>
    unfold countGetDUpto
    have h_cond : 0 ≤ (if (xs[n]?).getD fallback = target then (1 : Int) else 0) := by
      split <;> omega
    omega

/-! ### Counting contiguous segments -/

/-- Auxiliary function for `countSegments`: counts the number of contiguous segments
of value `x` in a list, given whether we are currently in such a segment. -/
def countSegmentsGo {α : Type} [DecidableEq α] (x : α) : List α → Bool → Nat
  | [], _ => 0
  | y :: ys, in_seg =>
    if y = x then
      (if in_seg then 0 else 1) + countSegmentsGo x ys true
    else
      countSegmentsGo x ys false

/-- Count the number of contiguous segments of value `x` in a list.
Segments are maximal contiguous runs of elements equal to `x`. -/
def countSegments {α : Type} [DecidableEq α] (a : List α) (x : α) : Nat :=
  countSegmentsGo x a false

@[simp] lemma countSegments_nil {α : Type} [DecidableEq α] (x : α) :
    countSegments [] x = 0 := by
  unfold countSegments
  rfl

/-- If the head of a list differs from `x`, prepending it does not change the segment count. -/
lemma countSegments_cons_of_ne {α : Type} [DecidableEq α] (y x : α) (a : List α) (h : y ≠ x) :
    countSegments (y :: a) x = countSegments a x := by
  unfold countSegments
  have hgo : countSegmentsGo x (y :: a) false = countSegmentsGo x a false := by
    calc
      countSegmentsGo x (y :: a) false
          = (if y = x then (if false then 0 else 1) + countSegmentsGo x a true
             else countSegmentsGo x a false) := rfl
      _ = countSegmentsGo x a false := by rw [if_neg h]
  rw [hgo]

/-- A singleton list `[x]` has exactly one segment of `x`. -/
lemma countSegments_singleton_eq {α : Type} [DecidableEq α] (x : α) :
    countSegments [x] x = 1 := by
  unfold countSegments
  calc
    countSegmentsGo x [x] false
        = (if x = x then (if false then 0 else 1) + countSegmentsGo x [] true
           else countSegmentsGo x [] false) := rfl
    _ = ((if false then 0 else 1) + countSegmentsGo x [] true) := by simp
    _ = (1 + countSegmentsGo x [] true) := by simp
    _ = (1 + 0) := rfl
    _ = 1 := by simp

/-- If `x` is not in the list, then `countSegments a x = 0`. -/
lemma countSegments_eq_zero_of_not_mem {α : Type} [DecidableEq α] (a : List α) (x : α) (h : x ∉ a) :
    countSegments a x = 0 := by
  induction a with
  | nil => exact countSegments_nil x
  | cons y ys ih =>
    have hx : y ≠ x := by
      intro heq; apply h; simp [heq]
    have hni : x ∉ ys := fun hm => h (by simp [hm])
    rw [countSegments_cons_of_ne y x ys hx]
    exact ih hni

/-! ### Value removal cost -/

/-- Compute the number of operations needed to remove all elements not equal to `x`
from a list, leaving only a contiguous block of `x` values.
Returns `a.length + 1` if `x` does not appear in `a`. -/
def valueRemovalCost {α : Type} [DecidableEq α] (a : List α) (x : α) : Nat :=
  let segs := countSegments a x
  if segs = 0 then
    a.length + 1
  else
    let left := if a.head? = some x then 1 else 0
    let right := if a.getLast? = some x then 1 else 0
    segs + 1 - left - right

@[simp] lemma valueRemovalCost_nil {α : Type} [DecidableEq α] (x : α) :
    valueRemovalCost [] x = 1 := by
  unfold valueRemovalCost countSegments countSegmentsGo
  rfl

/-! ### Dot product -/

/-- The dot product of the first `n` elements of two lists.
    `dotPrefix a b n = ∑_{i=0}^{n-1} a[i] * b[i]`, where out-of-bounds access
    returns `0`. This is the prefix version of the full dot product of two lists. -/
def dotPrefix {α : Type u} [Semiring α] (a b : List α) : Nat → α
  | 0 => 0
  | i+1 => dotPrefix a b i + (a[i]?).getD 0 * (b[i]?).getD 0

/-! ### Prefix operations -/

/-- The length of a filtered prefix is bounded by the prefix length `n`.
For any list `l`, filter `f`, and natural number `n`, `((l.take n).filter f).length ≤ n`. -/
lemma length_filter_take_le (l : List α) (f : α → Bool) (n : Nat) :
    ((l.take n).filter f).length ≤ n := by
  calc
    ((l.take n).filter f).length ≤ (l.take n).length := List.length_filter_le f (l.take n)
    _ = n ⊓ l.length := List.length_take n l
    _ ≤ n := Nat.min_le_left _ _

/-- Count elements equal to `v` in the first `i` elements of `a`.
Equivalent to `(a.take i).count v`. -/
def prefixCount {α : Type _} [DecidableEq α] (a : List α) (i : Nat) (v : α) : Nat :=
  (a.take i).count v

/-- If `l.length = n`, then `l.take n = l`. -/
lemma take_of_length_eq {α : Type _} (l : List α) (n : Nat) (h : l.length = n) : l.take n = l := by
  have hle : l.length ≤ n := by omega
  exact List.take_of_length_le hle

/-- Taking the full length of a list returns the list unchanged: `s.take s.length = s`.
This is the special case of `take_of_length_eq` when `n = l.length`. -/
lemma take_length_eq_self {α : Type _} (s : List α) : s.take s.length = s :=
  List.take_of_length_le (le_refl s.length)

/-- Counting an element in the prefix of length `s.length` is the same as counting in `s` itself.
Equivalent to `(s.take s.length).count a = s.count a`. -/
lemma count_take_length_eq_count {α : Type _} [DecidableEq α] (s : List α) (a : α) :
    (s.take s.length).count a = s.count a := by
  rw [take_length_eq_self]

/-- When the prefix length equals the list length, `prefixCount` equals the full `count`. -/
lemma prefixCount_of_length_eq {α : Type _} [DecidableEq α] (a : List α) (n : Nat) (v : α)
    (hlen : a.length = n) : prefixCount a n v = a.count v := by
  unfold prefixCount
  rw [take_of_length_eq a n hlen]

/-! ### Rightmost/leftmost index of a value -/

/-- Find the rightmost index `i < n` where `s[i]? = some v`, scanning downwards from `n`.
Returns `0` if no such index is found (or if the matching index is exactly `0` —
the caller must disambiguate; typically this is used when at least one occurrence
is known to exist in the range `[0, n)` and the default `0` represents the earliest
possible position / no earlier match found).

For example, `rightmostIdx [1, 0, 1] 1 3 = 2`. -/
def rightmostIdx {α : Type u} [DecidableEq α] (s : List α) (v : α) : Nat → Nat
  | 0 => 0
  | n+1 =>
    if s[n]? = some v then n
    else rightmostIdx s v n

/-- Find the leftmost index `i ≥ start` where `s[i]? = some v`.
Returns `s.length - 1` if no such index exists (or if `start ≥ s.length`).

For example, `leftmostIdx [1, 0, 1] 0 0 = 1`. -/
def leftmostIdx {α : Type u} [DecidableEq α] (s : List α) (v : α) (start : Nat) : Nat :=
  if h : start < s.length then
    if s[start]? = some v then start
    else leftmostIdx s v (start + 1)
  else
    s.length - 1
termination_by s.length - start
decreasing_by
  omega
@[deprecated rightmostIdx (since := "2026-08-07")]
def rightmost_one (s : List Nat) : Nat → Nat := rightmostIdx s 1
@[deprecated leftmostIdx (since := "2026-08-07")]
def leftmost_zero (s : List Nat) (start : Nat) : Nat := leftmostIdx s 0 start
/-- `rightmostIdx s v n ≤ n` — the rightmost index of `v` in the first `n` positions
is at most `n`. -/
lemma rightmostIdx_le_n {α : Type u} [DecidableEq α] (s : List α) (v : α) (n : Nat) :
    rightmostIdx s v n ≤ n := by
  induction n with
  | zero =>
    unfold rightmostIdx
    exact Nat.zero_le 0
  | succ n ih =>
    unfold rightmostIdx
    split
    · apply Nat.le_succ
    · exact Nat.le_trans ih (Nat.le_succ _)

/-- If `start ≤ s.length` and `0 < s.length`, then `leftmostIdx s v start < s.length`. -/
lemma leftmostIdx_lt_length {α : Type u} [DecidableEq α] (s : List α) (v : α) (start : Nat)
    (hpos : 0 < s.length) (h_start : start ≤ s.length) :
    leftmostIdx s v start < s.length := by
  unfold leftmostIdx
  split
  · rename_i hlt
    split
    · rename_i heq
      exact hlt
    · rename_i hne
      have h_next : start + 1 ≤ s.length := by omega
      exact leftmostIdx_lt_length s v (start + 1) hpos h_next
  · rename_i hge
    have : s.length - 1 < s.length := by omega
    exact this
termination_by s.length - start
decreasing_by
  omega

/-! ### zipWithState -/

/-- Zip two lists where a state (initialized to `init`) is threaded through the computation.
At each step, the function `f` receives the current state, the current `x` from `xs`, and the
current `y` from `ys`, producing an output element. The state is then updated to the current `y`
for the next step. Results are collected in a list of the same length as the shorter input list.

This is useful when each element's computation depends on the previous element of `ys`. -/
def zipWithState {α β γ : Type _} (init : β) (f : β → α → β → γ) (xs : List α) (ys : List β) : List γ :=
  match xs, ys with
  | x :: xs', y :: ys' => f init x y :: zipWithState y f xs' ys'
  | _, _ => []

/-- The length of `zipWithState init f xs ys` equals `xs.length` when the two input lists
have the same length. -/
lemma zipWithState_length {α β γ : Type _} (init : β) (f : β → α → β → γ) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (zipWithState init f xs ys).length = xs.length := by
  induction' xs with x xs' ih generalizing init ys
  · simp [zipWithState]
  · cases ys with
    | nil => simp at h
    | cons y ys' =>
      have h_len' : xs'.length = ys'.length := by simpa using h
      simp [zipWithState, ih y ys' h_len']

/-! ### Cost from first positive

Process a list from left to right computing a cumulative cost. Once a positive
element is encountered (the "start"), each subsequent positive element contributes
its full value and each zero / non-positive element contributes `1`.
Elements before the first positive contribute nothing. The last element always
contributes `0` (it cannot be reduced further since there is no element after it
to receive its value).

This pattern appears in problems like CF 1705B ("Mark the Dust Sweeper"),
where operations are counted to consolidate positive values toward the end of a list. -/

/-- Compute the total cost from the first positive element onward.
For a list `a`, scan left to right with a boolean flag `started`:

* If the current element is positive, add it to the cost and set `started := true`.
* If the current element is not positive but `started` is true, add `1`.
* Otherwise (not started and not positive), move on with cost `0`.
* The last element always contributes `0`.

This generalizes the `min_operations` / `suffix_cost` pattern from CF 1705B. -/
def costFromFirstPositive {α : Type} [LT α] [OfNat α 0] [OfNat α 1] [Add α]
    [DecidablePred (fun a : α => a > 0)] (a : List α) : α :=
  go a false
where
  go : List α → Bool → α
    | [], _ => 0
    | [_], _ => 0
    | ai :: rest, started =>
        if ai > 0 then
          ai + go rest true
        else if started then
          1 + go rest true
        else
          go rest false

/-- A function on lists with a boolean state `started` is equal to
`costFromFirstPositive.go` if and only if it satisfies the same recursive equations.
This provides a functional induction / equational reasoning principle for
proving properties of `costFromFirstPositive`. -/
theorem costFromFirstPositive_eq_of_equations
    {α : Type} [LT α] [OfNat α 0] [OfNat α 1] [Add α]
    [DecidablePred (fun a : α => a > 0)]
    (reference : List α → Bool → α)
    (h_nil : ∀ started, reference [] started = 0)
    (h_singleton : ∀ a started, reference [a] started = 0)
    (h_cons : ∀ a b rest started,
      reference (a :: b :: rest) started =
        if a > 0 then a + reference (b :: rest) true
        else if started then 1 + reference (b :: rest) true
        else reference (b :: rest) false) :
    ∀ s started, costFromFirstPositive.go s started = reference s started := by
  intro s
  induction s with
  | nil =>
      intro started
      simpa [costFromFirstPositive.go] using (h_nil started).symm
  | cons a rest ih =>
      cases rest with
      | nil =>
          intro started
          simpa [costFromFirstPositive.go] using (h_singleton a started).symm
      | cons b rest =>
          intro started
          change
            (if a > 0 then a + costFromFirstPositive.go (b :: rest) true
            else if started then 1 + costFromFirstPositive.go (b :: rest) true
            else costFromFirstPositive.go (b :: rest) false) =
            reference (a :: b :: rest) started
          rw [h_cons]
          by_cases ha : a > 0
          · simp only [ha, ↓reduceIte]
            rw [ih true]
          · by_cases hs : started
            · simp only [ha, hs, ↓reduceIte]
              rw [ih true]
            · simp [ha, hs, ih false]

/-! ### Run length at index -/

/-- Length of the contiguous run of elements equal to `val` in `a` that ends at index `i`.
Specifically, returns the largest `k` such that for all `j` with `i - k + 1 ≤ j ≤ i`,
`a[j]? = some val`. If `a[i]? ≠ some val`, returns `0`.
If `i = 0` and `a[0]? = some val`, returns `1`.
Otherwise, recurses on `i-1` to count backwards.

Example: `runLenEndingAt [1,0,0,1] 0 2 = 2` (two consecutive zeros ending at index 2). -/
def runLenEndingAt {α : Type _} [DecidableEq α] (a : List α) (val : α) (i : Nat) : Nat :=
  match a[i]? with
  | none => 0
  | some v =>
    if v ≠ val then 0
    else if i = 0 then 1
    else if a[i - 1]? = some val then runLenEndingAt a val (i - 1) + 1
    else 1
termination_by i
decreasing_by
  simp_wf
  omega

/-- `runLenEndingAt a val i ≤ i + 1` — the run length never exceeds the prefix length. -/
lemma runLenEndingAt_le_succ {α : Type _} [DecidableEq α] (a : List α) (val : α) (i : Nat) :
    runLenEndingAt a val i ≤ i + 1 := by
  induction' i using Nat.strong_induction_on with i ih
  unfold runLenEndingAt
  split
  · omega
  · rename_i v
    split
    · omega
    · split
      · omega
      · split
        · have hlt : i - 1 < i := by omega
          have hrec := ih (i - 1) hlt
          omega
        · omega

/-! ### `minimumOr` — a fallback-based minimum operation

`minimumOr` computes the minimum element of a list with an explicit fallback value
for the empty list. Unlike `List.minimum?`, the algorithm uses `Min α` (rather than
`LinearOrder α`) and uses a direct equality check against `fallback` to detect the
empty-list case during recursion. This means that if an element of the list equals
`fallback`, the result may be `fallback` even for non-empty lists — callers that
need to distinguish "empty list" from "element equals fallback" should use the
hypothesis `minimumOr fallback xs ≠ fallback`.

This pattern appears in problems where a sentinel value (e.g., `-1`) represents
"no valid answer," and the goal is to find the minimum among a computed set of
candidate values. -/

/-- Compute the minimum of `xs`, or return `fallback` if `xs` is empty.
Uses `min` from `Min α` rather than `≤` from `LinearOrder α`, allowing it to work
with types that have `Min` but not necessarily a full linear order (though most
useful theorems require `LinearOrder` for ordering properties). -/
def minimumOr [Min α] [DecidableEq α] (fallback : α) : List α → α
  | [] => fallback
  | x :: xs =>
      let y := minimumOr fallback xs
      if y = fallback then x else min x y

/-- If every element of `xs` is strictly greater than `fallback`, then
`minimumOr fallback xs = fallback` implies `xs` is empty (i.e., no element is in `xs`).
This is the contrapositive-in-disguise: when `fallback` is a strict lower bound,
the only way `minimumOr` can return `fallback` is if the list was empty. -/
lemma minimumOr_eq_fallback_no_mem [LinearOrder α] [DecidableEq α] {fallback : α}
    {xs : List α} (hlow : ∀ x, x ∈ xs → fallback < x)
    (h : minimumOr fallback xs = fallback) :
    ∀ x, x ∉ xs := by
  induction xs with
  | nil =>
      intro x hx
      simp at hx
  | cons x xs ih =>
      have hxlow : fallback < x := hlow x (by simp)
      simp only [minimumOr] at h
      by_cases hy : minimumOr fallback xs = fallback
      · have hxEq : x = fallback := by
          simp [hy] at h
          exact h
        rw [hxEq] at hxlow
        exact False.elim ((lt_irrefl fallback) hxlow)
      · by_cases hxy : x ≤ minimumOr fallback xs
        · have hxEq : x = fallback := by
            simp [hy, min_def, hxy] at h
            exact h
          rw [hxEq] at hxlow
          exact False.elim ((lt_irrefl fallback) hxlow)
        · have hyEq : minimumOr fallback xs = fallback := by
            simp [hy, min_def, hxy] at h
          exact (hy hyEq).elim

/-- If `minimumOr fallback xs ≠ fallback`, then the result is actually an element of `xs`.
Together with `minimumOr_le_of_mem`, this establishes that `minimumOr` returns a
minimum element that belongs to the list (when it differs from `fallback`). -/
lemma minimumOr_mem_of_ne [LinearOrder α] [DecidableEq α] {fallback : α} {xs : List α}
    (h : minimumOr fallback xs ≠ fallback) :
    minimumOr fallback xs ∈ xs := by
  induction xs with
  | nil =>
      simp [minimumOr] at h
  | cons x xs ih =>
      simp only [minimumOr]
      by_cases hy : minimumOr fallback xs = fallback
      · simp [hy]
      · by_cases hxy : x ≤ minimumOr fallback xs
        · simp [hy, min_def, hxy]
        · simp [hy, min_def, hxy, ih hy]

/-- If all elements of `xs` are strictly greater than `fallback`, and
`minimumOr fallback xs ≠ fallback` (i.e., the list is non-empty and at least
one element differs from `fallback`), then `minimumOr fallback xs` is a lower bound
for all elements of `xs`. -/
lemma minimumOr_le_of_mem [LinearOrder α] [DecidableEq α] {fallback : α} {xs : List α}
    (hlow : ∀ x, x ∈ xs → fallback < x) (hne : minimumOr fallback xs ≠ fallback) :
    ∀ x, x ∈ xs → minimumOr fallback xs ≤ x := by
  induction xs with
  | nil =>
      simp [minimumOr] at hne
  | cons x xs ih =>
      intro v hv
      simp only [minimumOr] at hne ⊢
      have hlowTail : ∀ y, y ∈ xs → fallback < y := by
        intro y hy
        exact hlow y (by simp [hy])
      by_cases hy : minimumOr fallback xs = fallback
      · have hNoTail := minimumOr_eq_fallback_no_mem hlowTail hy
        simp [hy] at hv ⊢
        rcases hv with rfl | hvTail
        · exact le_rfl
        · exact (hNoTail v hvTail).elim
      · have ihle := ih hlowTail hy
        rw [if_neg hy]
        rw [List.mem_cons] at hv
        rcases hv with hvHead | hvTail
        · rw [hvHead]
          exact min_le_left x (minimumOr fallback xs)
        · exact le_trans (min_le_right x (minimumOr fallback xs)) (ihle v hvTail)
/-! ### `pairwiseMap_specificDuplicate` — cartesian product with a function -/

/-- Map a binary function `f` over all pairs `(x, y)` with `x ∈ xs` and `y ∈ ys`,
returning a list of results. Equivalent to `(xs.product ys).map (fun (x, y) => f x y)`
but avoids creating intermediate `Prod` values. -/
def pairwiseMap_specificDuplicate (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  xs.flatMap fun x => ys.map fun y => f x y
/-! ### zipWith length when lists have equal length -/

/-- When two lists have equal length, the result of `zipWith` has that same length.
This is a corollary of `List.length_zipWith` specialized to equal-length inputs. -/
lemma length_zipWith_eq_left {α β γ : Type _} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (h : l₁.length = l₂.length) :
    (List.zipWith f l₁ l₂).length = l₁.length := by
  rw [List.length_zipWith, h, Nat.min_self]

/-- The length of `(List.range l.length).zip l` equals `l.length`.
This is a common pattern in competitive programming when pairing indices with elements:
the zip of `[0, …, n-1]` with a list of length `n` also has length `n`.
Follows from `List.length_zip` and `List.length_range`. -/
lemma length_zip_range {α : Type u} (l : List α) : ((List.range l.length).zip l).length = l.length := by
  rw [List.length_zip, List.length_range l.length, Nat.min_self]

/-- If an index `k` is in bounds for `l.map f`, it is also in bounds for the original list `l`.
This follows immediately from `List.length_map` which says mapping does not change
the length of the list. -/
lemma lt_of_lt_length_map {α β : Type _} (l : List α) (f : α → β) (k : Nat)
    (h : k < (l.map f).length) : k < l.length := by
  simpa [List.length_map] using h

/-! ### `prefixSumMap_specificDuplicate` — prefix sum of a mapped function over a list

`prefixSumMap_specificDuplicate f xs n` computes `∑_{k < n} f xs[k]`, i.e., the sum of `f` applied to
the first `n` elements of `xs`. Defined as `((xs.take n).map f).sum`.
This generalizes the prefix-sum-after-mapping pattern that appears in many
competitive-programming problems (e.g., LeetCode 2483). -/

/-- Prefix sum of `f` applied to the first `n` elements of `xs`:
`prefixSumMap_specificDuplicate f xs n = ∑_{k < n} f xs[k]`.
Equivalent to `prefixSum_specificDuplicate (xs.map f) n`. -/
def prefixSumMap_specificDuplicate {α β : Type} [AddCommMonoid β] (f : α → β) (xs : List α) (n : Nat) : β :=
  ((xs.take n).map f).sum

@[simp]
lemma prefixSumMap_zero {α β : Type} [AddCommMonoid β] (f : α → β) (xs : List α) :
    prefixSumMap_specificDuplicate f xs 0 = 0 := by
  simp [prefixSumMap_specificDuplicate]

/-- If `f x = g x` for all `x`, then `prefixSumMap_specificDuplicate f xs n = prefixSumMap_specificDuplicate g xs n`. -/
lemma prefixSumMap_congr {α β : Type} [AddCommMonoid β] (f g : α → β) (xs : List α) (n : Nat)
    (h : ∀ x, f x = g x) : prefixSumMap_specificDuplicate f xs n = prefixSumMap_specificDuplicate g xs n := by
  have hfg : f = g := funext h
  subst hfg; rfl

/-! ### Drop lemmas

These lemmas help reason about `List.drop` when the result is known to be non-empty
(i.e., when `xs.drop n` is a cons `a :: as`). They provide the three natural
consequences: the index is in bounds, the head element, and the tail.

We also provide lemmas connecting in-bounds indexed access to membership in `drop`:
- `mem_drop_getElem_of_index`: if `k` is in bounds and `n ≤ k`, then `l[k] ∈ l.drop n`.
- `exists_getElem_of_mem_drop`: if `x ∈ l.drop n`, then `x = l[k]` for some `k` with `n ≤ k < l.length`. -/

/-- If `k < l.length` and `n ≤ k`, then `l[k]` is a member of `l.drop n`.
This is a convenient form of `List.mem_drop_iff_getElem` when the index `k` is known directly. -/
lemma mem_drop_getElem_of_index {α : Type u} (l : List α) (k n : Nat) (hk_len : k < l.length) (hk_n : n ≤ k) :
    l[k] ∈ l.drop n := by
  rw [List.mem_drop_iff_getElem]
  have h_exists : ∃ d, k = n + d := Nat.exists_eq_add_of_le hk_n
  rcases h_exists with ⟨d, hk_eq⟩
  refine ⟨d, ?_, ?_⟩
  · have : d + n = k := by omega
    rw [this]
    exact hk_len
  · simp [hk_eq]

/-- If `x ∈ l.drop n`, then there exists an index `k` with `n ≤ k < l.length` such that `l[k] = x`.
This is the converse of `mem_drop_getElem_of_index`. -/
lemma exists_getElem_of_mem_drop {α : Type u} (l : List α) (x : α) (n : Nat) (h : x ∈ l.drop n) :
    ∃ (k : Nat) (hk_len : k < l.length), n ≤ k ∧ l[k] = x := by
  rw [List.mem_drop_iff_getElem] at h
  rcases h with ⟨j, hm, h_eq⟩
  have hm' : n + j < l.length := by
    simpa [add_comm] using hm
  refine ⟨n + j, hm', by omega, ?_⟩
  simp [h_eq]

/-- If `xs.drop n` equals `a :: as`, then `n` is less than the length of `xs`. -/
lemma drop_eq_cons_lt_length {α : Type} (xs : List α) (n : Nat) (a : α) (as : List α)
    (h : xs.drop n = a :: as) : n < xs.length := by
  by_contra h'
  have hle : xs.length ≤ n := by omega
  have hnil : xs.drop n = [] := List.drop_eq_nil_of_le hle
  rw [hnil] at h
  simp at h

/-- If `xs.drop n` equals `a :: as`, then `as` equals `xs.drop (n+1)`. -/
lemma tail_eq_of_drop_eq_cons {α : Type} (xs : List α) (n : Nat) (a : α) (as : List α)
    (h : xs.drop n = a :: as) : as = xs.drop (n + 1) := by
  calc
    as = (a :: as).tail := by simp
    _ = (xs.drop n).tail := by rw [h]
    _ = xs.drop (n + 1) := by rw [List.tail_drop]

/-- If `xs.drop n` equals `a :: as`, then `a` equals the element at index `n`. -/
lemma head_eq_of_drop_eq_cons {α : Type} (xs : List α) (n : Nat) (a : α) (as : List α)
    (h : xs.drop n = a :: as) : a = xs.get ⟨n, drop_eq_cons_lt_length xs n a as h⟩ := by
  have h_ne_nil : xs.drop n ≠ [] := by rw [h]; simp
  calc
    a = (a :: as).head (by simp) := by simp
    _ = (xs.drop n).head h_ne_nil := by simp [h]
    _ = xs.get ⟨n, drop_eq_cons_lt_length xs n a as h⟩ := by
      simp [List.head_drop]

  /-- When `n` is an in-bounds index in `l`, the `headD` of `l.drop n` with default `d`
  equals `l.getD n d`. This connects the structural `drop` operation with the indexed `getD`
  access. Useful for proofs that need to extract the first element of a suffix of a list. -/
  lemma headD_drop_eq_getD {α : Type u} (l : List α) (n : Nat) (d : α) (hn : n < List.length l) :
      (List.drop n l).headD d = l.getD n d := by
    induction' n with k ih generalizing l
    · cases l
      · simp at hn
      · simp
    · cases l
      · simp at hn
      · rename_i head tail
        simp at hn
        have h_lt : k < List.length tail := by omega
        simp [ih tail h_lt]

/-! ### Maximum ascending difference

These functions compute the maximum value of `xs[j] - xs[i]` where `i < j` —
the largest difference where the later element is larger than the earlier one.
This is the classic algorithm for "Best Time to Buy and Sell Stock" (LeetCode 121)
and appears in any problem requiring the maximum increase in a monotonic scan. -/

/-- Auxiliary fold that computes the maximum ascending difference in a list.
Scans from left to right, tracking `min_val` (the minimum element seen so far)
and `max_diff` (the maximum difference found). At each element `p`:
`max_diff` is updated to `max max_diff (p - min_val)`;
`min_val` is updated to `min min_val p`.
Returns `max_diff` when the list is exhausted. -/
def maxAscendingDiffAux {α : Type u} [LinearOrderedAddCommGroup α] (xs : List α) (min_val : α) (max_diff : α) : α :=
  match xs with
  | [] => max_diff
  | p :: ps =>
    let new_max := max max_diff (p - min_val)
    let new_min := min min_val p
    maxAscendingDiffAux ps new_min new_max

/-- The maximum ascending difference in a list: the largest value of `xs[j] - xs[i]`
where `i < j`. Returns `0` if the list is empty or nonincreasing.
For `x :: xs'`, initializes the scan with `min_val := x` and `max_diff := 0`. -/
def maxAscendingDiff {α : Type u} [LinearOrderedAddCommGroup α] (xs : List α) : α :=
  match xs with
  | [] => 0
  | x :: xs' => maxAscendingDiffAux xs' x 0

/-! ### Permutation and take

If a list is a permutation of `range n`, then any element in its first `k` elements
is less than `n`. This is useful for reasoning about sorted permutations
(e.g., in k-weakest-rows problems). -/

/-- If `l` is a permutation of `List.range n`, then every element in `l.take k` is
less than `n`. This follows because `List.range n` only contains numbers `< n`,
and permutation preserves the set of elements. -/
lemma lt_of_mem_take_of_perm_range {l : List ℕ} {n k : ℕ} (hperm : l.Perm (List.range n))
    {x : ℕ} (h : x ∈ l.take k) : x < n := by
  have hmem_l : x ∈ l := (List.take_sublist k l).subset h
  have hmem_range : x ∈ List.range n := (hperm.mem_iff).mp hmem_l
  exact List.mem_range.mp hmem_range

/-! ### Counting windows by sum predicate

`countWindowsSumWhere xs k n p` counts how many windows of size `k` in the first `n`
elements of `xs` have a sum satisfying Boolean predicate `p`. This generalizes the
"count subarrays of size k with sum ≥ threshold * k" pattern from LeetCode 1343
and similar sliding-window counting problems. -/

/-- Count the number of windows of size `k` in the first `n` elements of `xs`
whose sum satisfies predicate `p`. Returns `0` if `n = 0` or `n < k`
(no window of size `k` fits).

A window starting at index `i` covers elements `xs[i..i+k-1]`, and its sum is
computed via `segmentSum_specificDuplicate xs i k`. The predicate `p` receives the window sum.

Example: `countWindowsSumWhere [1, 3, 2, 6, -1, 4, 1, 8, 2] 3 9 (λ s => s ≥ 6)`
counts windows of size 3 whose sum is at least 6. -/
def countWindowsSumWhere {α : Type _} [AddCommMonoid α] (xs : List α) (k n : Nat) (p : α → Bool) : Nat :=
  if n = 0 ∨ n < k then 0
  else
    countWindowsSumWhere xs k (n - 1) p +
    (if p (segmentSum_specificDuplicate xs (n - k) k) then 1 else 0)
termination_by n
decreasing_by
  omega

/-! ### Sum vs length bound

When every element of a list is at least `1`, the sum is at least the length.
This is a fundamental inequality used to establish lower bounds in allocation
and counting problems (e.g., "each child gets at least one candy" → total candies ≥
number of children). -/

/-- If every element of `l : List Int` is at least `1`, then `l.sum ≥ l.length` (as integers).
This is the basic "each unit contributes at least 1" inequality for the integer sum of a list. -/
lemma sum_ge_length_of_all_ge_one (l : List Int) (h : ∀ x ∈ l, x ≥ 1) : (l.sum : Int) ≥ (l.length : Int) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp
    have hx : x ≥ 1 := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≥ 1 := by
      intro y hy; apply h y; simp [hy]
    have ih' := ih hxs
    omega

/-! ### Game-theoretic optimal difference (take 1-3 game)

`gameTakeDiff values` computes the optimal score difference in a two-player,
zero-sum, perfect-information game played on `values : List α`. On each turn,
the current player chooses to take 1, 2, or 3 elements from the front of the list,
adding their sum to their score. The opponent then plays optimally on the remaining
list. The return value is the maximum score difference the current player can achieve
(the current player's total minus the opponent's total), assuming both play optimally.

Recurrence:
- `gameTakeDiff [] = 0`
- For `v1 :: rest`, take 1: `v1 - gameTakeDiff rest`
- If possible, take 2: `v1 + v2 - gameTakeDiff (rest.drop 1)`
- If possible, take 3: `v1 + v2 + v3 - gameTakeDiff (rest.drop 2)`
- Result is the maximum of all available options.

This generalizes the recurrence from LeetCode 1406 (Stone Game III) to any
`LinearOrderedAddCommGroup`. -/
def gameTakeDiff {α : Type u} [LinearOrderedAddCommGroup α] (values : List α) : α :=
  match values with
  | [] => 0
  | v1 :: rest =>
    let r1 := gameTakeDiff rest
    match rest with
    | [] => v1 - r1
    | v2 :: rest' =>
      let r2 := gameTakeDiff rest'
      let take1 := v1 - r1
      let take2 := v1 + v2 - r2
      match rest' with
      | [] => max take1 take2
      | v3 :: rest'' =>
        let take3 := v1 + v2 + v3 - gameTakeDiff rest''
        max take1 (max take2 take3)

/-! ### Length positivity → non-empty

A convenience lemma bridging `1 ≤ l.length` (the common competitive programming
precondition form) to `l ≠ []` (the hypothesis required by many general theorems about
non-empty lists). -/

/-- If a list has length at least 1, it is not empty. -/
lemma length_pos_imp_ne_nil {α : Type u} {l : List α} (h : 1 ≤ l.length) : l ≠ [] := by
  intro h_eq
  have h_len : l.length = 0 := by simp [h_eq]
  omega

/-- If a list has length at least 1, then its length is positive.
This bridges the common competitive-programming precondition `1 ≤ l.length`
to `0 < l.length`, which is needed for constructing `Fin` indices. -/
lemma pos_of_one_le_length {α : Type u} (l : List α) (h : 1 ≤ l.length) : 0 < l.length := by omega

/-! ### anyPair_specificDuplicate — check if any pair in a list satisfies a binary predicate

`anyPair_specificDuplicate valid candidates` returns `true` iff there exist `left, right ∈ candidates`
such that `valid left right = true`. This is a general-purpose pair-check combinator
for exhaustive-search patterns where every possible pairing within a candidate set
needs to be tested. -/

/-- Returns `true` iff there exist `left, right ∈ candidates` such that
`valid left right = true`. Equivalent to `candidates.any (λ left => candidates.any (valid left))`. -/
def anyPair_specificDuplicate {α : Type} (valid : α → α → Bool) (candidates : List α) : Bool :=
  candidates.any (fun left => candidates.any (fun right => valid left right))

/-! ### pairwiseDistinctDisjoint — two lists with distinct elements and no overlap

`pairwiseDistinctDisjoint left right` asserts that `left` has no duplicate elements,
`right` has no duplicate elements, and no element of `left` equals any element of `right`.
The condition is stated using `Fin`-based index access, which is convenient for proofs
that reason about elements by their positions.

This is equivalent to `left.Nodup ∧ right.Nodup ∧ left.Disjoint right`
(for `[DecidableEq α]`), but the `Fin`-based formulation avoids the `DecidableEq` constraint
and is useful for index-based proofs (e.g., when working with `Pairwise` or `get`-based lemmas). -/

/-- `left` and `right` each have distinct elements and share no elements.
Uses `Fin`-based index access: for `i < j` in `left`, `left[i] ≠ left[j]`; same for `right`;
and for any `i` in `left`, `j` in `right`, `left[i] ≠ right[j]`. -/
def pairwiseDistinctDisjoint {α : Type} (left right : List α) : Prop :=
  (∀ i j : Fin left.length, i < j → left[i] ≠ left[j]) ∧
  (∀ i j : Fin right.length, i < j → right[i] ≠ right[j]) ∧
  (∀ (i : Fin left.length) (j : Fin right.length), left[i] ≠ right[j])

/-! ### Optimal interval game difference (interval DP)

`optimalIntervalDiff gain xs i j` computes the optimal score difference for the current
player in a two-player, zero-sum, perfect-information game played on the sublist
`xs[i..j]` (inclusive). On each turn, the current player chooses to take from the
left or right end of the remaining interval:

* Taking from the left: the player gains `gain xs (i+1) j` (the value of what remains
  after removing the left element) and then the opponent plays optimally, giving a
  net difference of `gain xs (i+1) j - optimalIntervalDiff gain xs (i+1) j`.
* Taking from the right: the player gains `gain xs i (j-1)` and the opponent plays
  optimally, giving `gain xs i (j-1) - optimalIntervalDiff gain xs i (j-1)`.

The player chooses the maximum of these two options. Returns `0` when `i ≥ j`
(empty interval, no moves remaining).

This DP pattern appears in stone-game problems (Stone Game VII, etc.) and
"Predict the Winner" problems where players remove from interval ends and gain
the sum of the remaining elements. By parameterizing the `gain` function, the same
recurrence structure is reused across problems with different scoring rules. -/

/-- Optimal score difference for a two-player interval game.
The `gain` function computes the immediate gain from the remaining interval
after a player takes from one end, and the recurrence subtracts the opponent's
optimal outcome from that gain. -/
def optimalIntervalDiff {α : Type u} [LinearOrderedAddCommGroup α]
    (gain : List α → Nat → Nat → α) (xs : List α) (i j : Nat) : α :=
  if i < j then
    let left := gain xs (i + 1) j - optimalIntervalDiff gain xs (i + 1) j
    let right := gain xs i (j - 1) - optimalIntervalDiff gain xs i (j - 1)
    max left right
  else
    0
termination_by j - i
decreasing_by
  all_goals omega

/-! ### `adjacentMap` — map over adjacent pairs

`adjacentMap f init xs` applies a binary function `f` to each adjacent pair of
elements in `xs`, using `init` as the first left argument. For `xs = [x₁, x₂, …, xₙ]`,
it produces `[f init x₁, f x₁ x₂, …, f x_{n-1} xₙ]`.

This is similar to `List.scanl` but uses the previous element (not the accumulated result)
as the first argument in each step. It appears in problems where each output element is
computed from the previous input element and the current input element
(e.g., LeetCode 2433 "Find the Original Array of Prefix XOR"). -/

/-- `adjacentMap f prev xs` maps over `xs` by applying `f` to consecutive elements,
starting with `(prev, head xs)` and continuing with `(xs[i], xs[i+1])`.
```
adjacentMap f prev [x₁, x₂, …, xₙ] = [f prev x₁, f x₁ x₂, …, f x_{n-1} xₙ]
``` -/
def adjacentMap (f : α → α → α) (prev : α) : List α → List α
  | [] => []
  | y :: ys => f prev y :: adjacentMap f y ys

/-- `adjacentMap` preserves length: the output list has the same length as the input. -/
lemma adjacentMap_length (f : α → α → α) (prev : α) (xs : List α) :
    (adjacentMap f prev xs).length = xs.length := by
  induction xs generalizing prev with
  | nil => simp [adjacentMap]
  | cons y ys ih => simp [adjacentMap, ih]

/-- Accessing `adjacentMap f prev xs` at index `0` returns `f prev xs[0]!`,
provided `xs` is nonempty. -/
lemma adjacentMap_get_zero [Inhabited α] (f : α → α → α) (prev : α) (xs : List α) (h : xs ≠ []) :
    (adjacentMap f prev xs)[0]! = f prev xs[0]! := by
  cases xs with
  | nil => simp at h
  | cons y ys => simp [adjacentMap]

/-! ### Greatest element bounded above

`greatestMember values bound` finds the greatest element `d ∈ values` such that
`d ≤ bound`, using `Nat.findGreatest`. Returns `0` if no element in `values`
satisfies `d ≤ bound`. This is a convenience wrapper around
`Nat.findGreatest (fun d => d ∈ values) bound` for list-based lookup.

Common in problems where you need the maximum value from a candidate list
that does not exceed a given bound (e.g., max distance between valid index pairs,
LeetCode 1855). -/

/-- Find the greatest element in `values` that is ≤ `bound`. Returns `0` if none found. -/
def greatestMember (values : List Nat) (bound : Nat) : Nat :=
  Nat.findGreatest (fun d => d ∈ values) bound

/-- The result of `greatestMember values bound` is either `0` or a member of `values`.
Uses `Nat.findGreatest_of_ne_zero` to deduce membership from a nonzero result. -/
lemma greatestMember_mem_or_zero {values : List Nat} {bound : Nat} :
    greatestMember values bound = 0 ∨ greatestMember values bound ∈ values := by
  unfold greatestMember
  by_cases h : Nat.findGreatest (fun d => d ∈ values) bound = 0
  · exact Or.inl h
  · exact Or.inr (Nat.findGreatest_of_ne_zero (P := fun d => d ∈ values) rfl h)

/-! ### Index-based min/max element predicates

`isMinAt xs idx` asserts that the element at index `idx` is a minimum of `xs`:
`xs[idx] ≤ xs[j]` for all `j`. `isMaxAt xs idx` is the analogous maximum property.
Both require the index to be in bounds.

These are the natural specification predicates for algorithms that find the position
of a minimum or maximum in a list (e.g., when the answer is an index, not a value).
They are generalized from `List Int` to any `LinearOrder α`.
-/

/-- `isMinAt xs idx` holds iff `idx < xs.length` and `xs[idx] ≤ xs[j]` for all `j`.
That is, the element at position `idx` is a minimum of the list. -/
def isMinAt {α : Type*} [LinearOrder α] (xs : List α) (idx : Nat) : Prop :=
  ∃ h : idx < xs.length, ∀ j : Fin xs.length, xs.get ⟨idx, h⟩ ≤ xs.get j

/-- `isMaxAt xs idx` holds iff `idx < xs.length` and `xs[j] ≤ xs[idx]` for all `j`.
That is, the element at position `idx` is a maximum of the list. -/

def isMaxAt {α : Type*} [LinearOrder α] (xs : List α) (idx : Nat) : Prop :=
  ∃ h : idx < xs.length, ∀ j : Fin xs.length, xs.get j ≤ xs.get ⟨idx, h⟩


/-! ### Duplicate detection

`containsDuplicate` is a `Bool`-valued predicate that checks whether a list
contains any element more than once. This is a computational version of `¬ Nodup l`
that works with a recursive membership check rather than constructing a `Finset`
or `Multiset`. It returns `true` iff `∃ i < j, l[i] = l[j]`.
-/

/-- Returns `true` if the list contains any element more than once.
    For `l = [x₁, x₂, …, xₙ]`, this checks whether `∃ i < j, l[i] = l[j]`.
    A computational version of `¬ Nodup l`.

    Example: `containsDuplicate [1, 2, 1] = true`, `containsDuplicate [1, 2, 3] = false`. -/
def containsDuplicate {α : Type u} [DecidableEq α] : List α → Bool
  | [] => false
  | x :: xs => if x ∈ xs then true else containsDuplicate xs

/-! ### Counting natural numbers in a range that appear in a list

`countNatsInRange nums start stop` counts how many `k` with `start ≤ k < stop` are
members of `nums`. This is useful for counting distinct values (without multiplicities)
that fall within a given numeric range — each range value contributes at most `1`,
regardless of how many times it appears in `nums`.

Example: `countNatsInRange [1,2,2,5] 1 4 = 2` (1 and 2 are in `[1,4)`, 5 is not,
and the duplicate `2` is only counted once per range value). -/

/-- Count how many natural numbers in `[start, stop)` appear in `nums`.
Each `k` with `start ≤ k < stop` contributes `1` if `k ∈ nums`, `0` otherwise.
Returns `0` when `start ≥ stop`. -/
def countNatsInRange (nums : List Nat) (start stop : Nat) : Nat :=
  if start < stop then
    (if start ∈ nums then 1 else 0) + countNatsInRange nums (start + 1) stop
  else
    0
termination_by stop - start
decreasing_by
  omega

lemma countNatsInRange_of_not_lt (nums : List Nat) (start stop : Nat) (h : ¬ start < stop) :
    countNatsInRange nums start stop = 0 := by
  unfold countNatsInRange
  simp [h]

lemma ite_one_le_one {p : Prop} [Decidable p] : (if p then (1 : Nat) else 0) ≤ 1 := by
  split <;> omega

lemma countNatsInRange_le_diff (nums : List Nat) (start stop : Nat) :
    countNatsInRange nums start stop ≤ stop - start := by
  refine @Nat.strong_induction_on
    (λ d => ∀ (s t : ℕ), t - s = d → countNatsInRange nums s t ≤ t - s)
    (stop - start) ?_ start stop rfl
  intro d IH s t h_eq
  subst h_eq
  by_cases hlt : s < t
  · unfold countNatsInRange
    simp [hlt]
    have h_sub_lt : t - (s + 1) < t - s := by omega
    have hrec : countNatsInRange nums (s + 1) t ≤ t - (s + 1) :=
      IH (t - (s + 1)) h_sub_lt (s + 1) t rfl
    have hsum : (if s ∈ nums then 1 else 0) + countNatsInRange nums (s + 1) t ≤
        1 + (t - (s + 1)) :=
      Nat.add_le_add ite_one_le_one hrec
    omega
  · rw [countNatsInRange_of_not_lt nums s t hlt]
    omega

/-- Counting positive values in `[1, bound]` that appear in `nums` is bounded by `bound`.
This follows from `countNatsInRange_le_diff` with `start = 1` and `stop = bound + 1`. -/
lemma countNatsInRange_one_le (nums : List Nat) (bound : Nat) :
    countNatsInRange nums 1 (bound + 1) ≤ bound := by
  have h := countNatsInRange_le_diff nums 1 (bound + 1)
  omega

/-! ### Last-index scan in a prefix

These functions find the rightmost index `i < n` in a list prefix where a condition holds.
They return `-1` as `Int` when no matching element is found, which is a convenient sentinel
for integer arithmetic (e.g., `bound - lastBad` gives the count of valid start positions).
This pattern appears in subarray-counting problems such as LeetCode 2444
("Count Subarrays With Fixed Bounds") where you need the last position of a minimum,
maximum, or out-of-range element in a sliding window. -/

/-- Find the last index `i < n` in a prefix of `nums` where the predicate `p` holds on
`nums[i]`. Scans from the right (index `n-1` down to `0`). Returns `-1` as `Int` if no
matching element is found in the first `n` elements. For `n = 0`, always returns `-1`. -/
def findLastIdxInPrefix {α : Type} [Inhabited α] (nums : List α) (p : α → Bool) : Nat → Int
  | 0 => -1
  | n' + 1 =>
    let val := (nums[n']?).getD default
    if p val then (n' : Int) else findLastIdxInPrefix nums p n'

/-- Find the last index `i < n` where `nums[i] = target`. Returns `-1` as `Int` if not found.
This is `findLastIdxInPrefix nums (fun x => x == target)`. -/
def lastIdxOfInPrefix {α : Type} [Inhabited α] [BEq α] (nums : List α) (target : α) : Nat → Int :=
  findLastIdxInPrefix nums (fun x => x == target)

/-! ### `count_at_least` — counting elements ≥ threshold

`count_at_least xs h` returns the number of elements in `xs` that are `≥ h`,
as a `ℤ` (to match typical `ℤ`-based problem specifications). This is a fundamental
operation for ranking / percentile / threshold queries on lists. -/

/-- Count how many elements in `xs` are at least `h` (≥ `h`). Returns `0` for empty list. -/
def count_at_least (xs : List ℤ) (h : ℤ) : ℤ :=
  match xs with
  | [] => 0
  | x :: t => (if x ≥ h then 1 else 0) + count_at_least t h

/-- `count_at_least` is always nonnegative. -/
lemma count_at_least_nonneg (xs : List ℤ) (h : ℤ) : 0 ≤ count_at_least xs h := by
  induction xs with
  | nil => simp [count_at_least]
  | cons head tail ih =>
    simp [count_at_least]
    split <;> omega

/-- `count_at_least xs h` never exceeds the list length. -/
lemma count_at_least_le_length (xs : List ℤ) (h : ℤ) : count_at_least xs h ≤ (xs.length : ℤ) := by
  induction xs with
  | nil => simp [count_at_least]
  | cons head tail ih =>
    simp [count_at_least]
    split <;> omega

/-- When the threshold exceeds the list length, the count must be strictly less than the threshold. -/
lemma count_at_least_lt_of_length_lt (xs : List ℤ) (h : ℤ) (hlt : (xs.length : ℤ) < h) :
    count_at_least xs h < h := by
  have hle := count_at_least_le_length xs h
  omega

/-! ### Mountain triplet

A mountain triplet in a list is three indices `i < j < k` (all within bounds) where
the middle element `nums[j]` is strictly greater than both `nums[i]` and `nums[k]`.
This is the combinatorial pattern behind "mountain array" problems (e.g., LeetCode 2909,
"Minimum Sum of Mountain Triplets I" and related problems about peaks in lists)
and is useful for any problem that seeks a peak-like triple in a list. -/

/-- Three indices `i < j < k` form a mountain triplet in `nums` if:
- `i < j < k < nums.length` (all indices are in bounds), and
- `nums[j]` is strictly greater than both `nums[i]` and `nums[k]`.

Uses `getDefault` for safe index access (returns `default` if out of bounds,
but this never happens since all indices are required to be in bounds). -/
def isMountainTriplet {α : Type u} [LT α] [Inhabited α] (nums : List α) (i j k : Nat) : Prop :=
  i < j ∧ j < k ∧ k < nums.length ∧
  nums.getDefault i < nums.getDefault j ∧
  nums.getDefault k < nums.getDefault j

/-! ### `with_length` — apply a function to a list and its own length

`with_length f ds` applies `f` to `ds` and `ds.length`. This is a convenience combinator
for algorithms that need both the list and its total length (e.g., prefix-based processing
where the length serves as a bound or index). -/

/-- Apply `f` to a list `ds` and its own length. `with_length f ds = f ds ds.length`. -/
def with_length {α β : Type} (f : List α → Nat → β) (ds : List α) : β :=
  f ds ds.length

@[simp]
lemma with_length_apply {α β : Type} (f : List α → Nat → β) (ds : List α) :
    with_length f ds = f ds ds.length := rfl

/-! ### Conditional prefix sum (masked/unmarked elements)

`sumUnmarkedPrefix xs mask stop` sums the first `stop` elements of `xs` where the
corresponding entry in the parallel `Bool` mask `mask` is `false` (i.e., "not marked").
This is a conditional prefix sum: only elements whose mask entry says "include"
(by being `false`, meaning "not marked for exclusion") are added to the sum.

`sumUnmarked xs mask` extends this to the full list.
Generalized from LeetCode 3080 ("Mark Elements on Array by Performing Queries"). -/

/-- Sum of the first `stop` elements of `xs` whose corresponding `mask` entry is `false`.
Uses indexed access via `getElem!`, so both `xs` and `mask` must be at least `stop` long.
For `stop = 0`, returns `0`.
This is a conditional prefix sum: elements are included iff `mask[i]` is `false`. -/
def sumUnmarkedPrefix {α : Type _} [AddMonoid α] [Inhabited α]
    (xs : List α) (mask : List Bool) (stop : ℕ) : α :=
  match stop with
  | 0 => 0
  | n + 1 =>
    sumUnmarkedPrefix xs mask n +
    (if mask[n]! then 0 else xs[n]!)

/-- Sum of all elements of `xs` whose corresponding `mask` entry is `false`.
Equivalent to `sumUnmarkedPrefix xs mask xs.length`. -/
def sumUnmarked {α : Type _} [AddMonoid α] [Inhabited α] (xs : List α) (mask : List Bool) : α :=
  sumUnmarkedPrefix xs mask xs.length

@[simp]
lemma sumUnmarkedPrefix_zero {α : Type _} [AddMonoid α] [Inhabited α]
    (xs : List α) (mask : List Bool) : sumUnmarkedPrefix xs mask 0 = 0 := rfl

/-! ### Index of minimum unmarked element in a prefix

`indexOfMinUnmarkedPrefix xs mask stop` finds the index (as a `Nat`) of the minimum
element among the first `stop` elements of `xs` that are not marked in the parallel
`Bool` mask `mask`. Ties are broken in favor of the smallest index. Returns `xs.length`
as a sentinel when no unmarked element exists in the prefix.

This is the "argmin over unmarked elements in a prefix" pattern, generalizing the
`best_in_prefix` function from LeetCode 3080 and similar index-finding algorithms
that operate on a parallel `Bool` mask. -/

/-- Index of the minimum element among the first `stop` elements of `xs` that are not
marked in the parallel `Bool` mask. Ties broken in favor of smallest index.
Returns `xs.length` (sentinel for "none found") if no unmarked elements exist in the prefix.
Uses indexed access via `getElem!`, so `xs` must be at least `stop` long. -/
def indexOfMinUnmarkedPrefix {α : Type _} [LinearOrder α] [Inhabited α]
    (xs : List α) (mask : List Bool) (stop : ℕ) : ℕ :=
  match stop with
  | 0 => xs.length
  | j + 1 =>
    let prev := indexOfMinUnmarkedPrefix xs mask j
    if mask[j]! then
      prev
    else if prev = xs.length then
      j
    else if xs[j]! < xs[prev]! ∨ (xs[j]! = xs[prev]! ∧ j < prev) then j else prev

@[simp]
lemma indexOfMinUnmarkedPrefix_zero {α : Type _} [LinearOrder α] [Inhabited α]
    (xs : List α) (mask : List Bool) : indexOfMinUnmarkedPrefix xs mask 0 = xs.length := rfl

/-! ### Circular list neighbors

These operations treat the list as a circular buffer: index `n-1`'s "next" is index `0`,
and index `0`'s "previous" is index `n-1`. The `circular_neighbors_differ` check is a
reusable building block for problems that examine circular/cyclic lists. -/

/-- Circular previous index in a list of length `n`:
for index `0`, wraps to `n-1`; otherwise returns `i-1`. -/
def circularPrev (n i : Nat) : Nat :=
  if i = 0 then n - 1 else i - 1

/-- Circular next index in a list of length `n`:
for index `n-1`, wraps to `0`; otherwise returns `i+1`. -/
def circularNext (n i : Nat) : Nat :=
  if i = n - 1 then 0 else i + 1

/-- Check if the element at index `i` in a circular list of length `n` differs from
both of its circular neighbors. `default` is the fallback value for out-of-bounds access.
Generalized from `spec_is_alternating` (LeetCode 3206). -/
def circular_neighbors_differ {α : Type} [DecidableEq α] (xs : List α) (default : α) (i n : Nat) : Bool :=
  xs.getD i default != xs.getD (circularPrev n i) default &&
  xs.getD i default != xs.getD (circularNext n i) default

/-! ### Permutation representation

`isPermutationRepr r p s` asserts that `r` is a permutation of `[0, …, s.length-1]`
(represented as a `List ℕ`) and `p` is the result of applying that permutation to `s`:
`p[i] = s[r[i]]` for each `i`.

This is useful for specifying sort/reshuffle correctness: the output `p` must be
a permutation of the input `s`, and `r` provides the concrete mapping of where each
element was placed.

Generalized from `is_reorder_of` in LeetCode 3111. -/

/-- `isPermutationRepr r p s` means:
1. `r`, `p`, and `s` all have the same length
2. Every element of `r` is a valid index into `s` (i.e., `< s.length`)
3. The elements of `r` are all distinct (so `r` is a permutation of `[0, s.length-1]`)
4. For each `i`, `p[i] = s[r[i]]` (using safe `getDefault` access) -/
def isPermutationRepr {α : Type u} [Inhabited α] (r : List ℕ) (p s : List α) : Prop :=
  r.length = s.length ∧
  p.length = s.length ∧
  (∀ (i : Nat), i < r.length → r.getDefault i < s.length) ∧
  (∀ (i j : Nat), i < j → j < r.length → r.getDefault i ≠ r.getDefault j) ∧
  (∀ (i : Nat), i < p.length → p.getDefault i = s.getDefault (r.getDefault i))

/-! ### `lengthApply` — apply a function to a list and its own length

`lengthApply f xs = f xs xs.length`. This is a convenience combinator for calling a
function `f : List α → Nat → β` that is parameterized by both the list and a length
(typically representing the number of elements to process from the list) with the
full list. When `f xs k` computes a result over the first `k` elements of `xs`,
`lengthApply f xs` gives the result over all elements. -/

/-! ### `take` / `drop` membership theorems

These lemmas relate list membership to `take` and `drop` operations with `getElem!`
(total access via `Inhabited`). They are useful when you have an index `i` and need
to know that `nums[i]!` belongs to `nums.take k` (when `i < k`) or to `nums.drop k`
(when `k ≤ i`). -/

/-- If `i < k` and `k ≤ nums.length`, then `nums[i]!` is in `nums.take k`.
This bridges index-based reasoning to membership-based reasoning for prefixes. -/
lemma mem_take_of_lt {α : Type u} [Inhabited α] (nums : List α) {k i : ℕ} (hi : i < k) (hk : k ≤ nums.length) :
    nums[i]! ∈ nums.take k := by
  have hi_len : i < nums.length := Nat.lt_of_lt_of_le hi hk
  have hi_take : i < (nums.take k).length := by
    rw [List.length_take]
    exact (Nat.lt_min.mpr ⟨hi, hi_len⟩)
  have h_take_eq : (nums.take k)[i] = nums[i] := by
    simpa using List.getElem_take nums (h := hi_take)
  have h_get_eq : nums[i]! = nums[i] := by
    simp [List.getElem!_eq_getElem_of_lt_specificDuplicate hi_len]
  have h_mem : (nums.take k)[i] ∈ nums.take k := List.getElem_mem hi_take
  rw [h_get_eq, ← h_take_eq]
  exact h_mem

/-- If `k ≤ b` and `b < nums.length`, then `nums[b]!` is in `nums.drop k`.
This bridges index-based reasoning to membership-based reasoning for suffixes. -/
lemma mem_drop_of_le {α : Type u} [Inhabited α] (nums : List α) {k b : ℕ} (hkb : k ≤ b) (hb : b < nums.length) :
    nums[b]! ∈ nums.drop k := by
  rcases Nat.exists_eq_add_of_le hkb with ⟨j, hb_eq⟩
  have hj_len : j + k < nums.length := by
    rw [add_comm, ← hb_eq]
    exact hb
  have h_val : nums[k + j] = nums[b]! := by
    subst hb_eq
    simp [List.getElem!_eq_getElem_of_lt_specificDuplicate hb]
  exact ((List.mem_drop_iff_getElem (i := k) (a := nums[b]!)).mpr ⟨j, hj_len, h_val⟩)

/-- If `k < nums.length`, then `nums.drop k` is nonempty.
This is a useful positive condition for algorithms that need to check
whether there are remaining elements after taking a prefix. -/
lemma drop_ne_nil_of_lt_len {α : Type u} (nums : List α) (k : ℕ) (h : k < nums.length) :
    nums.drop k ≠ [] := by
  have hlen_pos : 0 < (nums.drop k).length := by
    rw [List.length_drop]
    exact Nat.sub_pos_of_lt h
  intro h_empty
  rw [h_empty] at hlen_pos
  simp at hlen_pos

/-! ### Digits to natural number conversion

`digitsToNat digits` converts a list of decimal digits (most significant first)
to a natural number: `digitsToNat [1, 2, 3] = 123`. Implemented as a left fold
over the digit list accumulating `10 * acc + d` at each step. -/

/-- Convert a list of decimal digits (most significant first) to a natural number.
For example, `digitsToNat [1, 2, 3] = 123`. Uses a left fold:
`digitsToNat ds = ds.foldl (λ n d => 10 * n + d) 0`. -/
def digitsToNat (digits : List Nat) : Nat :=
  digits.foldl (λ n d => 10 * n + d) 0

@[simp]
lemma digitsToNat_nil : digitsToNat [] = 0 := rfl

lemma digitsToNat_cons (d : Nat) (ds : List Nat) :
    digitsToNat (d :: ds) = ds.foldl (λ n d' => 10 * n + d') d := by
  simp [digitsToNat, List.foldl]

/-- Apply a function `f : List α → Nat → β` to a list `xs` and its own length:
`lengthApply f xs = f xs xs.length`.
This is useful for calling prefix/suffix-parameterized functions on the full list. -/
def lengthApply (f : List α → Nat → β) (xs : List α) : β :=
  f xs xs.length

@[simp]
lemma lengthApply_eq (f : List α → Nat → β) (xs : List α) :
    lengthApply f xs = f xs xs.length := rfl

/-! ### Filtered sum (sum of elements satisfying a predicate)

`sumFilterPrefix p xs n` computes the sum of elements from the first `n` elements
of `xs` that satisfy the `Bool` predicate `p`. `sumFilter p xs` applies the predicate
to the entire list. These generalize the common pattern of summing only elements
with a given property (e.g., even elements) from a list prefix.

The `Bool` predicate form is suitable for `decide`-based reasoning and works with
any `AddCommMonoid`. -/

/-- Sum of elements from `xs.take n` that satisfy predicate `p`.
For example, `sumFilterPrefix (λ x => x % 2 = 0) [1,2,3,4] 3 = 2` (only the even
elements in the first 3: `[1,2,3]` → just `2`). -/
def sumFilterPrefix {α : Type _} [AddCommMonoid α] (p : α → Bool) (xs : List α) (n : Nat) : α :=
  ((xs.take n).filter p).sum

/-- Sum of elements from `xs` that satisfy predicate `p`.
Equivalent to `sumFilterPrefix p xs xs.length`. -/
def sumFilter {α : Type _} [AddCommMonoid α] (p : α → Bool) (xs : List α) : α :=
  sumFilterPrefix p xs xs.length

@[simp]
lemma sumFilterPrefix_zero {α : Type _} [AddCommMonoid α] (p : α → Bool) (xs : List α) :
    sumFilterPrefix p xs 0 = 0 := by
  simp [sumFilterPrefix]

@[simp]
lemma sumFilter_nil {α : Type _} [AddCommMonoid α] (p : α → Bool) :
    sumFilter p [] = 0 := by
  simp [sumFilter, sumFilterPrefix]

lemma sumFilter_eq_sumFilterPrefix_length {α : Type _} [AddCommMonoid α] (p : α → Bool) (xs : List α) :
    sumFilter p xs = sumFilterPrefix p xs xs.length := rfl

end List
