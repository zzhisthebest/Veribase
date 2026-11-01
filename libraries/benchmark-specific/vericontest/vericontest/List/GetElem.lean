import Mathlib

open List

namespace List

/-! ### `getElem!` membership lemmas

These lemmas bridge the total accessor `l[i]!` (which requires `Inhabited α` and
returns a default value for out-of-bounds indices) to standard list membership and
index-based access. -/

/-- When `i < l.length`, the element accessed via `((l[i]?).getD d)` is a member of `l`.
This bridges `getElem?` + `getD` to list membership for an in-bounds index.
The default value `d` is irrelevant because the index is valid. -/
lemma getElem?_getD_mem {α : Type _} (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    ((l[i]?).getD d) ∈ l := by
  rw [List.mem_iff_get]
  refine ⟨⟨i, hi⟩, ?_⟩
  simp [hi]

/-- When `i < l.length`, `l[i]!` (the total accessor) is a member of `l`. -/
lemma getElem!_mem_of_lt_specificDuplicate {α : Type _} [Inhabited α] (l : List α) {i : Nat} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [LawfulGetElem.getElem!_def]
  rw [List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

/-- Every element `x ∈ l` can be expressed as `l[i]!` for some in-bounds index `i`. -/
lemma exists_getElem!_eq_of_mem {α : Type _} [Inhabited α] {l : List α} {x : α} (hx : x ∈ l) :
    ∃ i : Nat, i < l.length ∧ l[i]! = x := by
  rcases (List.mem_iff_getElem.mp hx) with ⟨i, hi, hix⟩
  refine ⟨i, hi, ?_⟩
  rw [LawfulGetElem.getElem!_def]
  rw [List.getElem?_eq_getElem hi]
  exact hix

/-- An element `x` is in `l` iff there exists an in-bounds index `i` such that `l[i]! = x`.
This combines `getElem!_mem_of_lt_specificDuplicate` and `exists_getElem!_eq_of_mem` into a single `↔` lemma. -/
lemma mem_iff_getElem!_eq {α : Type _} [Inhabited α] (l : List α) (x : α) :
    x ∈ l ↔ ∃ (i : Nat), i < l.length ∧ l[i]! = x := by
  constructor
  · exact exists_getElem!_eq_of_mem
  · rintro ⟨i, hi, rfl⟩
    exact getElem!_mem_of_lt_specificDuplicate l hi

/-! ### Membership to `Fin` index

A bridge from `List` membership (`a ∈ l`) to a `Fin l.length` index `i` such that `l[i] = a`.
This is the forward direction of `List.mem_iff_get` using `l[i]` notation (which is
definitionally `l.get i` for `Fin` indices). -/

/-- From a proof of list membership, obtain a `Fin` index `i` such that `l[i] = a`.
Equivalently, the forward direction of `List.mem_iff_get`. -/
lemma mem_to_fin {α : Type} {l : List α} {a : α} (h : a ∈ l) : ∃ (i : Fin l.length), l[i] = a :=
  List.mem_iff_get.mp h

/-! ### Strictly sorted via `getElem!`

`SortedLT l` asserts that `l` is strictly increasing: for all `i < j` with `j < l.length`,
`l[i]! < l[j]!`. This is a direct index-based formulation that does not rely on
transitivity to extend from adjacent pairs. -/

/-- `SortedLT l` holds when `l` is strictly increasing when accessed via `getElem!`:
`∀ i j, i < j → j < l.length → l[i]! < l[j]!`. -/
def SortedLT {α : Type _} [LT α] [Inhabited α] (l : List α) : Prop :=
  ∀ i j : Nat, i < j → j < l.length → l[i]! < l[j]!

/-- If a list is `Sorted (· ≤ ·)` and `Nodup`, then for all `i < j` in bounds,
`l[i]! < l[j]!`. This bridges the standard library's `Sorted` predicate to the
`getElem!`-based strict ordering, i.e., `SortedLT`. -/
lemma sortedLT_of_sorted_nodup {α : Type _} [LinearOrder α] [Inhabited α]
    {l : List α} (hsorted : List.Sorted (· ≤ ·) l) (hnodup : l.Nodup)
    {i j : Nat} (hij : i < j) (hjlen : j < l.length) :
    l[i]! < l[j]! := by
  have hilen : i < l.length := by omega
  let fi : Fin l.length := ⟨i, hilen⟩
  let fj : Fin l.length := ⟨j, hjlen⟩
  have hfinlt : fi < fj := by
    dsimp [fi, fj]
    exact hij
  have hle : l.get fi ≤ l.get fj := hsorted.rel_get_of_lt hfinlt
  have hfin_ne : fi ≠ fj := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  have hne : l.get fi ≠ l.get fj := by
    intro hget
    exact hfin_ne ((List.Nodup.get_inj_iff hnodup).mp hget)
  have hgeti : l[i]! = l.get fi := by
    rw [LawfulGetElem.getElem!_def]
    rw [List.getElem?_eq_getElem hilen]
    rw [List.get_eq_getElem]
  have hgetj : l[j]! = l.get fj := by
    rw [LawfulGetElem.getElem!_def]
    rw [List.getElem?_eq_getElem hjlen]
    rw [List.get_eq_getElem]
  rw [hgeti, hgetj]
  exact lt_of_le_of_ne hle hne

/-! ### `List.ofFn` with `getD`

Convenience lemmas bridging `List.ofFn` (creating a list from a `Fin n → α` function)
with `getElem?` + `getD` for total index access with a default value. -/

/-- Accessing `(List.ofFn f)[i]?.getD d` when `i < n` returns `f ⟨i, h⟩`.
This combines `List.getElem?_ofFn` (from mathlib) with `getD`. -/
lemma getElem?_ofFn_getD {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (d : α) (h : i < n) :
    ((List.ofFn f)[i]?.getD d) = f ⟨i, h⟩ := by
  simp [List.getElem?_ofFn, h]

/-- `getD` on `List.ofFn f` at in-bounds index `i` returns `f ⟨i, h⟩`.
This is the direct `List.getD` formulation of `getElem?_ofFn_getD`.
When `i < n`, the default value `d` is irrelevant because the index is valid. -/
lemma getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]


/-! ### `getD` nonnegativity → membership nonnegativity

`forall_mem_nonneg_of_getD_nonneg` bridges from an index-wise nonnegativity condition
on `getD 0` to an element-wise nonnegativity condition on list membership.
This is useful when a property is stated in terms of `(l[i]?).getD 0` (common in
competitive-programming solutions) but the goal requires reasoning about `∀ x ∈ l, …`. -/

/-- If `0 ≤ (l[i]?).getD 0` for every in-bounds index `i`, then every element `x ∈ l` is
nonnegative. This bridges index-wise `getD`-based reasoning to element-wise reasoning. -/
lemma forall_mem_nonneg_of_getD_nonneg (l : List Int) (h : ∀ i < l.length, 0 ≤ (l[i]?).getD 0) :
    ∀ x ∈ l, 0 ≤ x := by
  intro x hx
  rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
  have h_nonneg_idx : 0 ≤ (l[i.val]?).getD 0 := h i.val i.2
  have h_get_eq : (l[i.val]?).getD 0 = l.get i := by
    simp [i.2]
  rw [← hi, ← h_get_eq]
  exact h_nonneg_idx

/-! ### `getElem?` + `toList`

A bridge between `getElem?` (which returns an `Option`) and `Option.toList`:
when the index is valid, `(l[i]?).toList` is the singleton `[l[i]]`. -/

/-- When `i < l.length`, `(l[i]?).toList = [l[i]]`.  This bridges `getElem?` to
`Option.toList`, converting an in-bounds `some` into a singleton list. -/
lemma getElem?_toList_eq_singleton {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (l[i]?).toList = [l[i]] := by
  have hget : l[i]? = some (l[i]) := List.getElem?_eq_getElem h
  simp [hget, Option.toList_some]

/-! ### `getElem?` + `getD` ≡ `getElem!`

When the index is in bounds, `(xs[index]?).getD fallback` coincides with `xs[index]!`,
regardless of the `fallback` value. This is a fundamental bridge between two common
indexing idioms. -/

/-- When `index < xs.length`, `(xs[index]?).getD fallback = xs[index]!`.
The `fallback` value is irrelevant because the index is in bounds. -/
lemma getElem?_getD_eq_getElem! {α : Type} [Inhabited α] (xs : List α)
    (fallback : α) {index : Nat} (hindex : index < xs.length) :
    (xs[index]?).getD fallback = xs[index]! := by
  simp [hindex, getElem!_pos xs index hindex]

/-- When the index is in bounds, the result of `(xs[i]?).getD` does not depend on the
fallback value: `(xs[i]?).getD fallback₁ = (xs[i]?).getD fallback₂`.
This is a convenience lemma for rewriting between two `getD` expressions with
different fallback values when the index is known to be valid.
Unlike `getElem?_getD_eq_getElem!`, this lemma does not require `[Inhabited α]`. -/
lemma getElem?_getD_eq_getD_of_lt {α : Type u} (xs : List α) (fallback₁ fallback₂ : α)
    {i : Nat} (hi : i < xs.length) :
    (xs[i]?).getD fallback₁ = (xs[i]?).getD fallback₂ := by
  simp [hi]

/-- When the index is in bounds, `(xs[i]?).getD d` equals `xs[i]` (the element itself,
not the `getElem!` total accessor). Unlike `getElem?_getD_eq_getElem!`, this lemma
does not require `[Inhabited α]` and uses the partial accessor `xs[i]` (with the
bound proof `hi` available via instance synthesis or explicit `'hi` notation). -/
lemma getElem?_getD_eq_getElem {α : Type u} (xs : List α) (i : Nat) (hi : i < xs.length) (d : α) :
    (xs[i]?).getD d = xs[i] := by
  simp [hi]

/-! ### `getElem?` + `getD` on mapped lists -/

/-- When `k < l.length`, the `getD` of a mapped list equals `f` applied to the element
at index `k` in the original list. This bridges `List.getElem?_map` to `getD`-based
reasoning and is useful in proofs where access is done via `(l[i]?).getD default`. -/
lemma getElem?_map_getD_of_lt {α β : Type _} (f : α → β) (l : List α) (k : Nat) (hk : k < l.length) (d : β) :
    ((l.map f)[k]?).getD d = f (l[k]) := by
  simp [List.getElem?_map, getElem?_eq_some_iff, hk]

/-! ### `getElem!` on mapped lists -/

/-- When `i < l.length`, the `getElem!` accessor commutes with `map`:
`(l.map f)[i]! = f (l[i]!)`. This is the `getElem!` counterpart of `List.getElem_map`
and bridges `map`-based reasoning to the total `getElem!` accessor commonly used in
competitive-programming proofs. -/
lemma getElem!_map_eq [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
    (l.map f)[i]! = f (l[i]!) := by
  have hlen : i < (l.map f).length := by
    simpa [List.length_map] using h
  have hpos1 : (l.map f)[i]! = (l.map f)[i] :=
    getElem!_pos (l.map f) i hlen
  have hpos2 : l[i]! = l[i] := getElem!_pos l i h
  rw [hpos1, hpos2, List.getElem_map f (h := hlen)]

/-! ### `get` nonnegativity via lower bound

These lemmas propagate nonnegativity from a lower bound through `List.get` (via `Fin`). -/

/-- If all elements of `xs` are ≥ `lower` and `0 ≤ lower`, then all elements are ≥ `0`.
This is a simple transitivity wrapper around `List.get`: when a list's elements are
bounded below by a nonnegative value, they are themselves nonnegative.
Generalized over any type with a `Preorder` and a `Zero`. -/
lemma get_nonneg_of_lower_bound {α : Type _} [Preorder α] [Zero α] {xs : List α} {lower : α}
    (hlower : 0 ≤ lower) (hget : ∀ i : Fin xs.length, lower ≤ xs.get i) :
    ∀ i : Fin xs.length, 0 ≤ xs.get i := by
  intro i
  exact le_trans hlower (hget i)

/-! ### `getElem!` on `range.map` -/

/-- When `i < m`, `((List.range m).map f)[i]! = f i`.
This is the `getElem!` counterpart of `List.getElem_map` for the specific case where
the underlying list is `range m`, which guarantees that `i` is in bounds and
`(range m)[i] = i`. -/
lemma getElem!_range_map_eq_specificDuplicate {α : Type} [Inhabited α] (m : Nat) (f : Nat → α) (i : Nat) (hi : i < m) :
    ((List.range m).map f)[i]! = f i := by
  have hi_len : i < ((List.range m).map f).length := by simpa using hi
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi_len, Option.getD_some]
  simp [List.getElem_map f (i := i) (h := hi_len)]

/-- When `i < n`, `((List.range n).map f)[i] = f i`.
This is the `getElem` counterpart of `getElem!_range_map_eq_specificDuplicate` and `getElem?_map_range_specificDuplicate`,
using the `i < ((List.range n).map f).length` proof rather than `i < n` for convenience
when the bound comes from the mapped list. -/
lemma getElem_range_map {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (h : i < ((List.range n).map f).length) :
    ((List.range n).map f)[i] = f i := by
  have hi_range : i < (List.range n).length := by
    simpa [List.length_map, List.length_range] using h
  calc
    ((List.range n).map f)[i] = f ((List.range n)[i]) := by
      simp [List.getElem_map]
    _ = f i := by
      simp [List.getElem_range i (by simpa [List.length_range] using hi_range)]

/-! ### `getD` bound propagates to membership -/

/-- If `xs.getD k default < n` for all in-bounds indices `k`, then every element `idx ∈ xs`
satisfies `idx < n`. This bridges index-wise `getD` bounds to element-wise membership bounds.
Commonly used when index-values are compared against a length bound
(e.g., verifying that all team members' indices are within the scores array). -/
lemma mem_lt_of_getD_lt {xs : List ℕ} {n default idx : ℕ}
    (hbound : ∀ k, k < xs.length → xs.getD k default < n) (hidx : idx ∈ xs) :
    idx < n := by
  rcases (List.mem_iff_get.mp hidx) with ⟨k, hk⟩
  have hbound_k := hbound k.val k.isLt
  have hbound_elem : xs.get k < n := by
    have hgetD : xs.getD k.val default = xs.get k := by
      simp [List.getD, k.isLt]
    rw [hgetD] at hbound_k
    exact hbound_k
  have hidx_elem : xs.get k = idx := hk
  rw [← hidx_elem]
  exact hbound_elem

/-! ### `get` / `getElem` with `Fin` index equality

When two `Fin` indices into the same list have equal underlying `.val`s,
the corresponding element accesses are equal. This bridges the `l.get f`
style with `l.get ⟨i, h⟩`. -/

/-- If `f : Fin l.length` satisfies `f.val = i` (and `i < l.length` is witnessed by `h`),
then `l.get f = l.get ⟨i, h⟩`. This is useful when converting between a `Fin` from context
and a `Fin` built inline from a bound proof. -/
lemma get_eq_get_of_val_eq {α : Type} {l : List α} {f : Fin l.length} {i : ℕ} {h : i < l.length}
    (hval : f.val = i) : l.get f = l.get ⟨i, h⟩ := by
  have hfeq : f = ⟨i, h⟩ := Fin.ext hval
  simp [hfeq]

/-! ### `getElem?` on cons lists with positive index

`List.getElem?_cons_zero` and `List.getElem?_cons_succ` (from the standard library)
handle the `0` and `n+1` cases respectively. The lemma below bridges from `0 < j`
hypotheses (common in `omega`-driven proofs) when the index is not immediately
in `n+1` form. -/

/-- When `0 < j`, the `j`-th element of a cons list equals the `j-1`-th element of the tail.
This rewrites `j` via `omega` and then delegates to `List.getElem?_cons_succ`. -/
lemma getElem?_cons_of_pos {α : Type} (x : α) (xs : List α) (j : ℕ) (h : 0 < j) :
    (x :: xs)[j]? = xs[j-1]? := by
  have hpos_eq : j = (j - 1) + 1 := by omega
  rw [hpos_eq]; simp

/-! ### `getD` with `Pairwise (· < ·)`

When a list is `Pairwise (· < ·)`, its elements are strictly increasing by index.
The following lemma provides a `getD`-based interface to this fact: for any indices
`i < j` that are both in bounds, the `getD` values respect the same ordering (the
default value `d` is irrelevant since both indices are valid). -/

/-- If `l` is `Pairwise (· < ·)` and `i < j < l.length`, then `l.getD i d < l.getD j d`.
The default value `d` does not affect the result because both indices are in bounds.
This bridges the structural `Pairwise` predicate to `getD`-based index access. -/
lemma getD_lt_getD_of_pairwise_lt {α : Type} [LT α] {l : List α} {d : α}
    (hp : List.Pairwise (· < ·) l) {i j : Nat}
    (hij : i < j) (hj : j < l.length) : l.getD i d < l.getD j d := by
  have hi : i < l.length := Nat.lt_trans hij hj
  rw [List.getD_eq_getElem _ d hi, List.getD_eq_getElem _ d hj]
  have hfin : (⟨i, hi⟩ : Fin l.length) < ⟨j, hj⟩ := hij
  have hget := (List.pairwise_iff_get.mp hp) ⟨i, hi⟩ ⟨j, hj⟩ hfin
  exact hget

/-! ### `Pairwise` via `getElem!`

A general lemma bridging `List.Pairwise r l` (for any relation `r`) to the total
`getElem!` accessor. Unlike `getD_lt_getD_of_pairwise_lt` (specialized to `(· < ·)`),
this version works for any binary relation and uses `getElem!`. -/

/-- If `l` is `Pairwise r` and `i < j` with `j < l.length`, then `r l[i]! l[j]!`.
This bridges the structural `Pairwise` predicate to the total `getElem!` accessor
for any relation `r : α → α → Prop`. -/
lemma pairwise_getElem! {α : Type _} [Inhabited α] {r : α → α → Prop} {l : List α}
    (hp : List.Pairwise r l) {i j : Nat} (hij : i < j) (hj : j < l.length) :
    r l[i]! l[j]! := by
  have hi : i < l.length := lt_trans hij hj
  rw [getElem!_pos l i hi]
  rw [getElem!_pos l j hj]
  exact (List.pairwise_iff_getElem.mp hp) i j hi hj hij

/-! ### `listGet` — total accessor with zero default

`listGet xs i` is a convenient shorthand for `(xs[i]?).getD 0`.  It returns the
element at index `i`, or `0` when the index is out of bounds.  This spelling is
common in competitive-programming solutions. -/

/-- Total accessor returning the `i`-th element of `xs`, or `0` if `i` is out of bounds.
Equivalent to `xs.getD i 0`. -/
def listGet {α : Type} [Zero α] (xs : List α) (i : Nat) : α :=
  (xs[i]?).getD 0

/-- `listGet` on the empty list always returns `0`. -/
lemma listGet_nil {α : Type} [Zero α] (i : Nat) : listGet ([] : List α) i = 0 := by
  unfold listGet
  simp

/-! ### `drop` decomposition at an index

`drop_eq_get_cons` decomposes `l.drop n` into the element at index `n` followed by
`l.drop (n + 1)`, when `n < l.length`. This is the key structural lemma for
reasoning about `drop` at a specific in-bounds index. -/

/-- When `n < l.length`, `l.drop n = l.get ⟨n, h⟩ :: l.drop (n + 1)`.
This decomposes the drop of the first `n` elements into the `n`-th element followed by
the rest. -/
lemma drop_eq_get_cons {α : Type} (l : List α) (n : Nat) (h : n < l.length) :
    l.drop n = l.get ⟨n, h⟩ :: l.drop (n + 1) := by
  induction' l with x xs ih generalizing n
  · exfalso; exact Nat.not_lt_zero _ h
  · match n with
    | 0 => rfl
    | n+1 =>
      have hn : n < xs.length := by
        simpa [List.length_cons] using h
      simpa using ih n hn

/-! ### `getD_map_range` — `getD` on `range.map` with `Zero`

`getD_map_range f n i hi` shows that `((List.range n).map f).getD i 0 = f i` when
`i < n`. This is the `getD` counterpart of `getElem_range_map` and
`getElem!_range_map_eq_specificDuplicate`, useful when access uses the `getD`-based total accessor
with a `Zero` instance for the fallback value (common in competitive programming). -/

/-- When `i < n`, `((List.range n).map f).getD i 0 = f i`.
The default value `0` (from `Zero α`) is irrelevant since the index is valid. -/
lemma getD_map_range {α : Type} [Zero α] (f : Nat → α) (n i : Nat) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  simp [hi]

/-! ### `Pairwise (· < ·)` via `Fin` get

When a list is `Pairwise (· < ·)`, its elements are strictly increasing by `Fin` index.
This lemma provides a direct `get`-based interface: for any `Fin` indices `i < j`,
`l.get i < l.get j`. Unlike `getD_lt_getD_of_pairwise_lt` (which uses `getD` with a
default value) and `pairwise_getElem!` (which uses `getElem!`), this version uses the
pure `get` accessor, making it the most natural bridge between `Pairwise` and
`StrictlySorted`. -/

/-- If `l` is `Pairwise (· < ·)`, then for any `Fin` indices `i < j`,
`l.get i < l.get j`. This bridges `Pairwise` structural strict ordering to the
`get`-based `Fin`-indexed `StrictlySorted` formulation. -/
lemma get_lt_of_pairwise_lt {α : Type} [LT α] {l : List α} (hp : List.Pairwise (· < ·) l)
    (i j : Fin l.length) (hij : i < j) : l.get i < l.get j := by
  have h := (List.pairwise_iff_getElem.mp hp) i.val j.val i.is_lt j.is_lt (by
    have : i.val < j.val := hij
    exact this)
  simp [h]

/-! ### `drop` length and emptiness lemmas

These lemmas relate the emptiness of `l.drop pos` to the relationship between
`pos` and `l.length`. They are useful for terminating induction over `drop`
(the drop is empty iff `pos = l.length`, and nonempty iff `pos < l.length`). -/

/-- If `l.drop pos = []` and `pos ≤ l.length`, then `pos = l.length`.
The converse `l.drop l.length = []` is `List.drop_length`. -/
lemma drop_eq_nil_of_pos_eq_length {α : Type _} (l : List α) (pos : Nat) (hpos_le : pos ≤ l.length)
    (hdrop : l.drop pos = []) : pos = l.length := by
  have hlen_drop : (l.drop pos).length = l.length - pos := List.length_drop pos l
  rw [hdrop] at hlen_drop
  simp at hlen_drop
  omega

/-- If `l.drop pos ≠ []` and `pos ≤ l.length`, then `pos < l.length`.
The direction `pos < l.length → l.drop pos ≠ []` is `List.drop_ne_nil_of_lt`. -/
lemma lt_length_of_drop_ne_nil {α : Type _} (l : List α) (pos : Nat) (hpos_le : pos ≤ l.length)
    (hne : l.drop pos ≠ []) : pos < l.length := by
  have hlen_drop : (l.drop pos).length = l.length - pos := List.length_drop pos l
  have hpos_drop : (l.drop pos).length > 0 := List.length_pos_of_ne_nil hne
  rw [hlen_drop] at hpos_drop
  omega

/-- If `l.drop n ≠ []`, then `n < l.length`. A simpler implication that does not
require `pos ≤ l.length` — the `drop ≠ []` condition alone forces the bound. -/
lemma lt_length_of_drop_ne_nil' {α : Type _} (l : List α) (n : Nat) (hne : l.drop n ≠ []) :
    n < l.length := by
  by_contra! hge
  have hnil : l.drop n = [] := List.drop_eq_nil_iff.mpr hge
  exact hne hnil

/-- If `l[i]? = some a` then `i < l.length`.
This is the forward direction of `List.getElem?_eq_some_iff`, extracted as a named lemma
for convenience in proofs that only need the index bound from a `getElem?` lookup result. -/
lemma getElem?_eq_some_implies_lt {α : Type} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : i < l.length :=
  ((List.getElem?_eq_some_iff (l := l) (i := i) (a := a)).mp h).1

/-! ### `getElem!` with `Fin` index bridge

When `i : Fin xs.length`, the total accessor `xs[i]!` equals the partial accessor
`xs[i.val]`. This bridges the two indexing styles used in competitive-programming proofs:
`getElem!` with a `Fin` index (common when enumerating over `Finset (Fin n)`) and
plain `getElem` with a `Nat` index (common with explicit `j < xs.length` hypotheses). -/

/-- `xs[i]! = xs[i.val]` when `i : Fin xs.length`.
Bridges the `Fin`-indexed total accessor (`getElem!`) to the `Nat`-indexed partial
accessor (`getElem`). The proof chains `getElem!_pos` (which reduces `xs[i]!` to
`xs.get i`) with `List.get_eq_getElem` (which converts `get` to `getElem`). -/
lemma getElem!_fin_eq_getElem {α : Type} [Inhabited α] (xs : List α) (i : Fin xs.length) :
    xs[i]! = xs[i.val] := by
  rw [getElem!_pos xs i i.isLt]
  change xs.get i = xs[i.val]
  rw [List.get_eq_getElem]

/-! ### `getD` from `∀` over `Fin`-indexed `getElem!`

When a property `P` holds for all `Fin`-indexed `getElem!` accesses, it also holds
for all `getD` accesses at in-bounds indices. This is a general bridge lemma that
works for any type `α` with `Inhabited` and any predicate `P : α → Prop`.
The fallback value is irrelevant since the index is in bounds. -/

/-- If `∀ i : Fin xs.length, P (xs[i]!)`, then for any in-bounds `j < xs.length` and any
fallback `d`, `P (xs.getD j d)`. This bridges `Fin`-indexed `getElem!` reasoning to
`getD`-based indexing, which is common in competitive-programming solutions. -/
lemma getD_of_forall_fin_getElem! {α : Type} [Inhabited α] (xs : List α) (d : α) (P : α → Prop)
    (h : ∀ i : Fin xs.length, P xs[i]!) {j : Nat} (hj : j < xs.length) :
    P (xs.getD j d) := by
  rw [List.getD_eq_getElem xs d hj]
  have h' := h (⟨j, hj⟩ : Fin xs.length)
  rwa [getElem!_fin_eq_getElem xs (⟨j, hj⟩ : Fin xs.length)] at h'

/-! ### `getElem` on appended mapped lists

When a list is built by concatenating two lists that have each been mapped
(possibly with different functions), accessing an element in the right-hand
portion simplifies to applying the right-hand function to the element at the
adjusted index in the right-hand list. -/

/-- When `i ≥ a.length` and the adjusted index `i - a.length` is in bounds in `b`,
the `i`-th element of `(a.map f ++ b.map g)` is `g` applied to the element of `b` at
index `i - a.length`. This is the right-side counterpart of using `List.getElem_append_right`
followed by `List.getElem_map` for the case where the left and right halves may have
different mapping functions. -/
lemma getElem_map_append_right {α β : Type} (f g : α → β) (a b : List α) (i : Nat)
    (hi : a.length ≤ i) (hb : i - a.length < b.length)
    (h : i < (a.map f ++ b.map g).length) :
    (a.map f ++ b.map g)[i] = g (b[i - a.length]'hb) := by
  rw [List.getElem_append_right (as := a.map f) (i := i) (by simpa using hi)]
  rw [List.getElem_map]
  simp

end List
