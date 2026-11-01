import Mathlib

open List

/-!
# Accumulator-based min/max over lists

`listMin_specificDuplicate lst acc` and `listMax_specificDuplicate lst acc` compute the minimum/maximum of a list
together with an initial accumulator. These are tail-recursive alternatives to
`foldl min`/`foldl max`. The accumulator pattern is useful for starting from a
specific initial value (e.g., the head of the list when scanning the tail).

Example: `listMin_specificDuplicate [3,1,4] 2 = 1` (the min of {2,3,1,4})
Example: `listMax_specificDuplicate [3,1,4] 2 = 4` (the max of {2,3,1,4})
-/

namespace List

/-! ### `listMin_specificDuplicate` and `listMax_specificDuplicate` definitions -/

/-- Compute the minimum of `lst` and `acc` using tail-recursive accumulator.
`listMin_specificDuplicate lst acc = min acc (minimum of lst)`. Generalized to any `LinearOrder`. -/
def listMin_specificDuplicate {α : Type} [LinearOrder α] (lst : List α) (acc : α) : α :=
  match lst with
  | [] => acc
  | x :: xs => listMin_specificDuplicate xs (min x acc)

/-- Compute the maximum of `lst` and `acc` using tail-recursive accumulator.
`listMax_specificDuplicate lst acc = max acc (maximum of lst)`. Generalized to any `LinearOrder`. -/
def listMax_specificDuplicate {α : Type} [LinearOrder α] (lst : List α) (acc : α) : α :=
  match lst with
  | [] => acc
  | x :: xs => listMax_specificDuplicate xs (max x acc)

/-! ### Accumulator bounds -/

/-- `listMin_specificDuplicate lst acc ≤ acc` — the result is at most the initial accumulator. -/
lemma listMin_le_acc {α : Type} [LinearOrder α] (lst : List α) (acc : α) : listMin_specificDuplicate lst acc ≤ acc := by
  induction' lst with x xs ih generalizing acc
  · rfl
  · dsimp [listMin_specificDuplicate]
    have hmin : min x acc ≤ acc := min_le_right _ _
    exact le_trans (ih (min x acc)) hmin

/-- `acc ≤ listMax_specificDuplicate lst acc` — the result is at least the initial accumulator. -/
lemma acc_le_listMax {α : Type} [LinearOrder α] (lst : List α) (acc : α) : acc ≤ listMax_specificDuplicate lst acc := by
  induction' lst with x xs ih generalizing acc
  · rfl
  · dsimp [listMax_specificDuplicate]
    have hmax : acc ≤ max x acc := le_max_right _ _
    exact le_trans hmax (ih (max x acc))

/-! ### Element bounds — listMin_specificDuplicate/listMax_specificDuplicate are lower/upper bounds -/

/-- Every element of `lst` is ≥ `listMin_specificDuplicate lst acc` — `listMin_specificDuplicate` is a lower bound for the list. -/
lemma listMin_le_get {α : Type} [LinearOrder α] (lst : List α) (acc : α) (j : Nat) (hj : j < lst.length) :
    listMin_specificDuplicate lst acc ≤ lst.get ⟨j, hj⟩ := by
  induction' lst with x xs ih generalizing acc j
  · exact (Nat.not_lt_zero j hj).elim
  · dsimp [listMin_specificDuplicate]
    cases' j with j
    · have h1 : listMin_specificDuplicate xs (min x acc) ≤ min x acc := listMin_le_acc xs (min x acc)
      have h2 : min x acc ≤ x := min_le_left _ _
      exact le_trans h1 h2
    · have hjxs : j < xs.length := by
        simp at hj; exact hj
      exact ih (min x acc) j hjxs

/-- Every element of `lst` is ≤ `listMax_specificDuplicate lst acc` — `listMax_specificDuplicate` is an upper bound for the list. -/
lemma get_le_listMax {α : Type} [LinearOrder α] (lst : List α) (acc : α) (j : Nat) (hj : j < lst.length) :
    lst.get ⟨j, hj⟩ ≤ listMax_specificDuplicate lst acc := by
  induction' lst with x xs ih generalizing acc j
  · exact (Nat.not_lt_zero j hj).elim
  · dsimp [listMax_specificDuplicate]
    cases' j with j
    · have h1 : x ≤ max x acc := le_max_left _ _
      have h2 : max x acc ≤ listMax_specificDuplicate xs (max x acc) := acc_le_listMax xs (max x acc)
      exact le_trans h1 h2
    · have hjxs : j < xs.length := by
        simp at hj; exact hj
      exact ih (max x acc) j hjxs

/-! ### Existence of element achieving the max -/

/-- Either `listMax_specificDuplicate lst acc = acc`, or some element of `lst` equals `listMax_specificDuplicate lst acc`.
This characterizes when the initial accumulator is already the maximum. -/
lemma exists_get_eq_listMax {α : Type} [LinearOrder α] (lst : List α) (acc : α) :
    listMax_specificDuplicate lst acc = acc ∨ (∃ (j : Nat) (hj : j < lst.length), lst.get ⟨j, hj⟩ = listMax_specificDuplicate lst acc) := by
  induction' lst with x xs ih generalizing acc
  · left; rfl
  · rw [listMax_specificDuplicate]
    rcases ih (max x acc) with (h | ⟨j, hj, h_eq⟩)
    · rw [h]
      by_cases hxle : acc ≤ x
      · have hm : max x acc = x := max_eq_left hxle
        right; refine ⟨0, by simp, ?_⟩
        simp [hm]
      · have hlt : x < acc := lt_of_not_ge hxle
        have hm : max x acc = acc := max_eq_right (le_of_lt hlt)
        left; exact hm
    · right; refine ⟨j + 1, by simp [hj], ?_⟩
      simpa using h_eq

/-! ### Convenience lemmas for the `x :: xs` case -/

/-- For `x :: xs`, every element is ≤ `listMax_specificDuplicate xs x` — `listMax_specificDuplicate` of the tail with head as acc
is an upper bound for the entire cons list. -/
lemma listMax_cons_ge_get {α : Type} [LinearOrder α] (x : α) (xs : List α) (j : Nat) (hj : j < (x :: xs).length) :
    (x :: xs).get ⟨j, hj⟩ ≤ listMax_specificDuplicate xs x := by
  cases' j with j
  · simp; exact acc_le_listMax xs x
  · have hj' : j < xs.length := by simp at hj; exact hj
    simpa using get_le_listMax xs x j hj'

/-- For `x :: xs`, every element is ≥ `listMin_specificDuplicate xs x` — `listMin_specificDuplicate` of the tail with head as acc
is a lower bound for the entire cons list. -/
lemma listMin_cons_le_get {α : Type} [LinearOrder α] (x : α) (xs : List α) (j : Nat) (hj : j < (x :: xs).length) :
    listMin_specificDuplicate xs x ≤ (x :: xs).get ⟨j, hj⟩ := by
  cases' j with j
  · simp; exact listMin_le_acc xs x
  · have hj' : j < xs.length := by simp at hj; exact hj
    simpa using listMin_le_get xs x j hj'

/-- There exists an element in `x :: xs` equal to `listMax_specificDuplicate xs x`.
This is the existential version of `listMax_cons_ge_get`: the bound is attained. -/
lemma listMax_cons_exists_get {α : Type} [LinearOrder α] (x : α) (xs : List α) :
    ∃ (j : Nat) (hj : j < (x :: xs).length), (x :: xs).get ⟨j, hj⟩ = listMax_specificDuplicate xs x := by
  rcases exists_get_eq_listMax xs x with (h_eq_acc | ⟨j, hj, h_eq⟩)
  · refine ⟨0, by simp, ?_⟩
    simp; exact h_eq_acc.symm
  · refine ⟨j + 1, by simp [hj], ?_⟩
    simpa using h_eq

/-! ### `maxWithDefault_specificDuplicate` / `minWithDefault_specificDuplicate` — non-tail-recursive max/min with explicit default

`maxWithDefault_specificDuplicate d lst` computes the maximum of `lst` and `d` using a recursive `max` fold:
`max x₁ (max x₂ (… (max xₙ d)))`. Returns `d` for the empty list. Unlike `listMax_specificDuplicate`,
this is not tail-recursive but matches the natural recursive decomposition, making
structural induction proofs straightforward.

`minWithDefault_specificDuplicate d lst` is the analogous minimum.

This pattern appears in problems requiring a sentinel-based max/min over `List Int`
with `Int.minInt`/`Int.maxInt` as defaults (e.g., LeetCode 1509). -/

/-- Compute the maximum of `lst` and `default` via recursive `max`:
`maxWithDefault_specificDuplicate default [x, y, z] = max x (max y (max z default))`.
Returns `default` for the empty list. -/
def maxWithDefault_specificDuplicate {α : Type} [LinearOrder α] (default : α) (lst : List α) : α :=
  match lst with
  | [] => default
  | x :: xs => max x (maxWithDefault_specificDuplicate default xs)

/-- Compute the minimum of `lst` and `default` via recursive `min`:
`minWithDefault_specificDuplicate default [x, y, z] = min x (min y (min z default))`.
Returns `default` for the empty list. -/
def minWithDefault_specificDuplicate {α : Type} [LinearOrder α] (default : α) (lst : List α) : α :=
  match lst with
  | [] => default
  | x :: xs => min x (minWithDefault_specificDuplicate default xs)

/-! ### Membership bounds for `maxWithDefault_specificDuplicate` / `minWithDefault_specificDuplicate` -/

/-- If `x ∈ s`, then `x ≤ maxWithDefault_specificDuplicate d s`.
The default `d` does not affect this bound — it is only used for the empty case. -/
lemma le_maxWithDefault_of_mem {α : Type} [LinearOrder α] {s : List α} {x d : α} (hx : x ∈ s) :
    x ≤ maxWithDefault_specificDuplicate d s := by
  induction s with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [maxWithDefault_specificDuplicate, List.mem_cons] at *
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- The default value `d` is always ≤ `maxWithDefault_specificDuplicate d s`.
This is a companion to `le_maxWithDefault_of_mem`: it says the sentinel itself is
a lower bound (not an upper bound). -/
lemma le_maxWithDefault_of_default {α : Type} [LinearOrder α] {s : List α} (d : α) :
    d ≤ maxWithDefault_specificDuplicate d s := by
  induction s with
  | nil => simp [maxWithDefault_specificDuplicate]
  | cons x xs ih =>
    unfold maxWithDefault_specificDuplicate
    exact le_trans ih (le_max_right _ _)

/-- If `d < maxWithDefault_specificDuplicate d s`, then there exists an element of `s` equal to the maximum.
This is the attainment lemma: when the maximum strictly exceeds the default, at least
one list element achieves it. Compare `maxWithDefault_eq_of_mem_and_forall_le`, which
requires knowing the specific element in advance. -/
lemma exists_mem_eq_maxWithDefault_of_lt_default {α : Type} [LinearOrder α] {s : List α} {d : α}
    (hgt : d < maxWithDefault_specificDuplicate d s) : ∃ x ∈ s, x = maxWithDefault_specificDuplicate d s := by
  induction s with
  | nil => simp [maxWithDefault_specificDuplicate] at hgt
  | cons x xs ih =>
    simp only [maxWithDefault_specificDuplicate] at hgt ⊢
    by_cases hle : maxWithDefault_specificDuplicate d xs ≤ x
    · refine ⟨x, by simp, ?_⟩
      exact (max_eq_left hle).symm
    · have hlt : x < maxWithDefault_specificDuplicate d xs := lt_of_not_ge hle
      have hm : max x (maxWithDefault_specificDuplicate d xs) = maxWithDefault_specificDuplicate d xs := max_eq_right hlt.le
      rw [hm] at hgt
      rcases ih hgt with ⟨z, hz, hz_eq⟩
      refine ⟨z, by simp [hz], ?_⟩
      rw [hz_eq, hm]

/-- If `x ∈ s`, then `minWithDefault_specificDuplicate d s ≤ x`.
The default `d` does not affect this bound — it is only used for the empty case. -/
lemma minWithDefault_le_of_mem_specificDuplicate {α : Type} [LinearOrder α] {s : List α} {x d : α} (hx : x ∈ s) :
    minWithDefault_specificDuplicate d s ≤ x := by
  induction s with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [minWithDefault_specificDuplicate, List.mem_cons] at *
    rcases hx with rfl | hx
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih hx)

/-! ### Upper/lower bound preservation -/

/-- If every element of `s` is ≤ `hi` and the default `d` is also ≤ `hi`,
then `maxWithDefault_specificDuplicate d s ≤ hi`. -/
lemma maxWithDefault_le_of_forall_le {α : Type} [LinearOrder α] {d hi : α} {s : List α}
    (h : ∀ x ∈ s, x ≤ hi) (hd : d ≤ hi) :
    maxWithDefault_specificDuplicate d s ≤ hi := by
  induction s with
  | nil => simp [maxWithDefault_specificDuplicate, hd]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≤ hi := by
      intro y hy; exact h y (by simp [hy])
    simp only [maxWithDefault_specificDuplicate]
    exact max_le hx (ih hxs)

/-- If `lo` is ≤ every element of `s` and `lo ≤ d` (the default), then
`lo ≤ minWithDefault_specificDuplicate d s`. -/
lemma le_minWithDefault_of_forall_le {α : Type} [LinearOrder α] {lo d : α} {s : List α}
    (h : ∀ x ∈ s, lo ≤ x) (hd : lo ≤ d) :
    lo ≤ minWithDefault_specificDuplicate d s := by
  induction s with
  | nil => simp [minWithDefault_specificDuplicate, hd]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, lo ≤ y := by
      intro y hy; exact h y (by simp [hy])
    simp only [minWithDefault_specificDuplicate]
    exact le_min hx (ih hxs)

/-! ### Attainment: when the bound is itself in the list -/

/-- If every element of `s` is ≤ `hi`, `hi` is itself an element of `s`,
and the default `d` is ≤ `hi`, then `maxWithDefault_specificDuplicate d s = hi`. -/
lemma maxWithDefault_eq_of_mem_and_forall_le {α : Type} [LinearOrder α] {d hi : α} {s : List α}
    (h : ∀ x ∈ s, x ≤ hi) (hm : hi ∈ s) (hd : d ≤ hi) :
    maxWithDefault_specificDuplicate d s = hi := by
  apply le_antisymm
  · exact maxWithDefault_le_of_forall_le h hd
  · exact le_maxWithDefault_of_mem hm

/-- If `lo` is ≤ every element of `s`, `lo` is itself an element of `s`,
and `lo ≤ d` (the default), then `minWithDefault_specificDuplicate d s = lo`. -/
lemma minWithDefault_eq_of_mem_and_forall_le {α : Type} [LinearOrder α] {lo d : α} {s : List α}
    (h : ∀ x ∈ s, lo ≤ x) (hm : lo ∈ s) (hd : lo ≤ d) :
    minWithDefault_specificDuplicate d s = lo := by
  apply le_antisymm
  · exact minWithDefault_le_of_mem_specificDuplicate hm
  · exact le_minWithDefault_of_forall_le h hd

/-! ### Simultaneous min and max with indices in a single pass

`MinMaxResult α` records the minimum value, its index, the maximum value, and its index
from a single traversal of the list. `minMax xs` computes this in one pass, which is more
efficient than calling separate min/max operations when both extremal values and their
positions are needed.

Theorems `minMax_min_spec` and `minMax_max_spec` certify that the result correctly
identifies the minimum and maximum elements of the (nonempty) list.
-/

/-- The result of computing both minimum and maximum in a single list traversal:
min value, min index, max value, max index. -/
structure MinMaxResult (α : Type*) where
  minVal : α
  minIdx : Nat
  maxVal : α
  maxIdx : Nat

/-- Compute the minimum and maximum (with their indices) of a list in a single pass.
For `[]`, returns `default` for all fields.
For `[x]`, returns `x` at index `0` for both min and max.
For `x :: y :: xs`, compares `x` with the `minMax` of `y :: xs` and adjusts indices
accordingly (adding `1` when the extremum comes from the tail).
-/
def minMax {α : Type*} [LinearOrder α] [Inhabited α] : List α → MinMaxResult α
  | [] => { minVal := default, minIdx := 0, maxVal := default, maxIdx := 0 }
  | [x] => { minVal := x, minIdx := 0, maxVal := x, maxIdx := 0 }
  | x :: y :: xs =>
    let r := minMax (y :: xs)
    { minVal := min x r.minVal
      minIdx := if x ≤ r.minVal then 0 else r.minIdx + 1
      maxVal := max x r.maxVal
      maxIdx := if r.maxVal ≤ x then 0 else r.maxIdx + 1 }

/-- Correctness of `minMax` for the minimum: for a non-empty list `xs`,
the element at `(minMax xs).minIdx` equals `(minMax xs).minVal`,
and `(minMax xs).minVal` is a lower bound for all elements of `xs`. -/
theorem minMax_min_spec {α : Type*} [LinearOrder α] [Inhabited α]
    (xs : List α) (hxs : xs ≠ []) :
    ∃ h : (minMax xs).minIdx < xs.length,
      xs.get ⟨(minMax xs).minIdx, h⟩ = (minMax xs).minVal ∧
        ∀ j : Fin xs.length, (minMax xs).minVal ≤ xs.get j := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [minMax]
    | cons y ys =>
      have hr := ih (by simp)
      rcases hr with ⟨hidx, heq, hall⟩
      by_cases hx : x ≤ (minMax (y :: ys)).minVal
      · refine ⟨by simp [minMax, hx], ?_, ?_⟩
        · simp [minMax, hx]
        · intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simp [minMax, hx]
          · simpa [minMax, hx, min_eq_left hx, List.get_cons_succ] using hx.trans (hall k)
      · have hlt : (minMax (y :: ys)).minVal < x := lt_of_not_ge hx
        refine ⟨by simpa [minMax, hx] using Nat.succ_lt_succ hidx, ?_, ?_⟩
        · simpa [minMax, hx, min_eq_right hlt.le, List.get_cons_succ] using heq
        · intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa [minMax, hx, min_eq_right hlt.le] using hlt.le
          · simpa [minMax, hx, min_eq_right hlt.le, List.get_cons_succ] using hall k

/-- Correctness of `minMax` for the maximum: for a non-empty list `xs`,
the element at `(minMax xs).maxIdx` equals `(minMax xs).maxVal`,
and `(minMax xs).maxVal` is an upper bound for all elements of `xs`. -/
theorem minMax_max_spec {α : Type*} [LinearOrder α] [Inhabited α]
    (xs : List α) (hxs : xs ≠ []) :
    ∃ h : (minMax xs).maxIdx < xs.length,
      xs.get ⟨(minMax xs).maxIdx, h⟩ = (minMax xs).maxVal ∧
        ∀ j : Fin xs.length, xs.get j ≤ (minMax xs).maxVal := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [minMax]
    | cons y ys =>
      have hr := ih (by simp)
      rcases hr with ⟨hidx, heq, hall⟩
      by_cases hx : (minMax (y :: ys)).maxVal ≤ x
      · refine ⟨by simp [minMax, hx], ?_, ?_⟩
        · simp [minMax, hx]
        · intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simp [minMax, hx]
          · simpa [minMax, hx, max_eq_left hx, List.get_cons_succ] using (hall k).trans hx
      · have hlt : x < (minMax (y :: ys)).maxVal := lt_of_not_ge hx
        refine ⟨by simpa [minMax, hx] using Nat.succ_lt_succ hidx, ?_, ?_⟩
        · simpa [minMax, hx, max_eq_right hlt.le, List.get_cons_succ] using heq
        · intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa [minMax, hx, max_eq_right hlt.le] using hlt.le
          · simpa [minMax, hx, max_eq_right hlt.le, List.get_cons_succ] using hall k

/-! ### `argmaxPrefixGetD` — index of maximum in a prefix using `getD 0`

`argmaxPrefixGetD s n` returns the index `i` (with `i < n`) such that
`(s[i]?).getD 0` is maximal among `(s[0]?).getD 0` through `(s[n-1]?).getD 0`.
When `n ≤ 1`, returns `0`. Ties are broken in favor of the **largest** index
(rightmost occurrence of the maximum).

This is the `getD`-based counterpart of `indexOfMaxInPrefix` (from `List`),
differing in two ways:
- Uses `getD 0` instead of `!` (requiring `Zero` instead of `Inhabited`)
- Breaks ties in favor of the rightmost index (whereas `indexOfMaxInPrefix`
  favors the leftmost/first occurrence)

This pattern appears in problems like LeetCode 3075 ("Maximize Happiness of
Selected Children"), where the algorithm repeatedly selects the maximum element
and marks it as consumed.
-/

/-- Returns the index of the maximum element in the first `n` positions of `s`,
using `getD 0` for safe access. Ties broken to the rightmost (largest) index. -/
def argmaxPrefixGetD {α : Type} [LinearOrder α] [Zero α] (s : List α) (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    let j := argmaxPrefixGetD s (n - 1)
    if (s[(n - 1)]?).getD 0 ≥ (s[j]?).getD 0 then
      n - 1
    else
      j
termination_by n

/-- The result of `argmaxPrefixGetD s n` is always strictly less than `n` when `n > 0`.
This ensures the returned index is always within the prefix `0..n-1`. -/
lemma argmaxPrefixGetD_lt {α : Type} [LinearOrder α] [Zero α] (s : List α) {n : Nat} (hn : 0 < n) :
    argmaxPrefixGetD s n < n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold argmaxPrefixGetD
    split
    · omega
    · simp
      split
      · omega
      · have hn1_pos : 0 < n - 1 := by omega
        have hlt : argmaxPrefixGetD s (n - 1) < n - 1 := ih (n - 1) (by omega) hn1_pos
        omega

/-! ### Positive offset is not in the list

If you add a positive amount `ε` to the maximum of a list, the result is strictly
larger than every element and therefore not in the list. This lemma generalizes
the common pattern `listMax_specificDuplicate nums + 1 ∉ nums` for integer lists. -/

/-- If `ε > 0`, then `maxWithDefault_specificDuplicate d l + ε` is not an element of `l`.
This is a fundamental property: the maximum of a list plus a positive offset
exceeds every element, so it cannot be in the list. -/
lemma maxWithDefault_add_pos_not_mem {α : Type} [LinearOrderedAddCommGroup α] (d : α) {l : List α} (ε : α)
    (hεpos : 0 < ε) : maxWithDefault_specificDuplicate d l + ε ∉ l := by
  intro hmem
  have hle := le_maxWithDefault_of_mem (hx := hmem) (d := d)
  have hlt : maxWithDefault_specificDuplicate d l < maxWithDefault_specificDuplicate d l + ε :=
    lt_add_of_pos_right _ hεpos
  exact not_lt.mpr hle hlt

end List
