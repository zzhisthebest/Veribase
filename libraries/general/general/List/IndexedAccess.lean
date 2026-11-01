import Mathlib

namespace List


/-! ### `getElem?` and `getElem!` on `range` and `map` -/

/-- If `i < n`, then `(List.range n)[i]! = i`. -/
lemma getElem!_range (n i : Nat) (h : i < n) : (List.range n)[i]! = i := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_range h]

/-- When the index is in bounds, `getElem!` equals `getElem`:
`l[i]! = l[i]` whenever `i < l.length`. -/
lemma getElem!_eq_getElem_of_lt {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l[i]! = l[i] := by
  simp [List.getElem?_eq_getElem h]

/-- If all elements accessed by `getElem` equal `v`, then all `getElem!` also equal `v`. -/
lemma getElem!_eq_of_forall_getElem_eq {l : List α} {v : α} [Inhabited α]
    (h : ∀ i (hi : i < l.length), l[i] = v) : ∀ i (hi : i < l.length), l[i]! = v := by
  intro i hi
  rw [getElem!_eq_getElem_of_lt hi, h i hi]

/-- When the index is in bounds, `l[i]!` is a member of `l`. -/
lemma getElem!_mem_of_lt {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_eq_getElem_of_lt h]
  exact List.getElem_mem h

/-- If `i` is in bounds for `l.take k`, then `(l.take k)[i]!` is a member of the original list `l`. -/
lemma take_getElem!_mem {α : Type _} [Inhabited α] (l : List α) (k i : Nat) (h : i < (l.take k).length) :
    (l.take k)[i]! ∈ l :=
  List.mem_of_mem_take (getElem!_mem_of_lt h)

/-- `l[i]!` equals `l.getD i default`, where `default` is the `Inhabited` default for `α`.
This provides a direct connection between the `!` out-of-bounds-safe index syntax and
the `getD` function with an explicit default value. -/
lemma getElem!_eq_getD {α : Type _} [Inhabited α] (l : List α) (i : Nat) : l[i]! = l.getD i default := by
  simp [List.getD]

/-- In a sorted list, if `i < j` are valid indices, then `l[i]!` relates to `l[j]!`
via the sort relation. This bridges `List.Sorted.rel_get_of_lt` (which works over `Fin`)
with the `getElem!` notation commonly used in benchmark code. -/
lemma Sorted.rel_get!_of_lt {α : Type} [Inhabited α] {r : α → α → Prop} {l : List α}
    (h_sorted : List.Sorted r l) {i j : Nat} (hij : i < j) (hi : i < l.length) (hj : j < l.length) :
    r (l[i]!) (l[j]!) := by
  have hfin : (⟨i, hi⟩ : Fin l.length) < (⟨j, hj⟩ : Fin l.length) := by
    simpa using hij
  have hrel := h_sorted.rel_get_of_lt hfin
  have hget_i : l[i]! = l.get ⟨i, hi⟩ := by simp [hi]
  have hget_j : l[j]! = l.get ⟨j, hj⟩ := by simp [hj]
  rw [hget_i, hget_j]
  exact hrel

/-- In a sorted list, if `i < j` are valid indices, then `l.getD i d` and `l.getD j d`
relate via the sort relation. This is the `getD` variant of `Sorted.rel_get!_of_lt`,
which works with any explicit default value `d` instead of requiring `[Inhabited α]`. -/
lemma Sorted.rel_getD_of_lt {α : Type} {r : α → α → Prop} {l : List α} {d : α}
    (h_sorted : List.Sorted r l) {i j : Nat} (hij : i < j) (hi : i < l.length) (hj : j < l.length) :
    r (l.getD i d) (l.getD j d) := by
  have hfin : (⟨i, hi⟩ : Fin l.length) < (⟨j, hj⟩ : Fin l.length) := by
    simpa using hij
  have hrel := h_sorted.rel_get_of_lt hfin
  have hi_eq : l.getD i d = l.get ⟨i, hi⟩ := by
    dsimp [List.getD]
    simpa using congrArg (·.getD d) (List.get?_eq_get hi)
  have hj_eq : l.getD j d = l.get ⟨j, hj⟩ := by
    dsimp [List.getD]
    simpa using congrArg (·.getD d) (List.get?_eq_get hj)
  rw [hi_eq, hj_eq]
  exact hrel

/-- In a sorted list, if `i < j` and `l[i]? = some a` and `l[j]? = some b`, then `r a b`.
This is the `getElem?` (Option-based) variant of `Sorted.rel_get!_of_lt`, which
does not require `[Inhabited α]` — the bounds are implicitly given by the `getElem?`
equalities rather than explicit `i < l.length` arguments. -/
lemma Sorted.rel_of_getElem?_lt {α : Type} {r : α → α → Prop} {l : List α}
    (h_sorted : List.Sorted r l) {i j : Nat} {a b : α}
    (h_lt : i < j) (ha : l[i]? = some a) (hb : l[j]? = some b) : r a b := by
  rcases List.getElem?_eq_some_iff.mp ha with ⟨hi_len, ha_eq⟩
  rcases List.getElem?_eq_some_iff.mp hb with ⟨hj_len, hb_eq⟩
  have h_fin_lt : (⟨i, hi_len⟩ : Fin l.length) < ⟨j, hj_len⟩ :=
    Fin.mk_lt_mk.mpr h_lt
  have h_rel := h_sorted.rel_get_of_lt h_fin_lt
  simpa [ha_eq, hb_eq] using h_rel

/-- In a list sorted by `(· ≤ ·)`, if `i ≤ j`, `l[i]? = some a`, and `l[j]? = some b`,
then `a ≤ b`. This is the non-strict (`i ≤ j`) variant of `Sorted.rel_of_getElem?_lt`,
using `getElem?` (Option-based) indexing rather than `getElem!`.
We require a `LinearOrder α` because `≤` must be reflexive for the `i = j` case. -/
lemma Sorted.le_of_getElem?_le {α : Type} [LinearOrder α] {l : List α}
    (h_sorted : List.Sorted (· ≤ ·) l) {i j : Nat} {a b : α}
    (h_le : i ≤ j) (ha : l[i]? = some a) (hb : l[j]? = some b) : a ≤ b := by
  rcases Nat.eq_or_lt_of_le h_le with (h_eq | h_lt)
  · subst h_eq
    have : a = b := by simpa [ha] using hb
    subst this; exact le_refl _
  · exact Sorted.rel_of_getElem?_lt h_sorted h_lt ha hb

/-- In a list sorted by `(· ≤ ·)`, the elements at valid indices `a ≤ b` satisfy
`l[a]! ≤ l[b]!`. This is the non-strict version of `Sorted.rel_get!_of_lt`,
which only handles strict `a < b`. -/
lemma Sorted.le_getElem_getElem {α : Type u} [LinearOrder α] [Inhabited α] {l : List α}
    (hs : List.Sorted (· ≤ ·) l) (a b : Nat) (ha : a < l.length) (hb : b < l.length) (hle : a ≤ b) :
    l[a]! ≤ l[b]! := by
  have hp := (List.pairwise_iff_get (R := (· ≤ ·))).mp hs
  rcases Nat.lt_or_eq_of_le hle with (hlt | heq)
  · have hge := hp ⟨a, ha⟩ ⟨b, hb⟩ (Fin.mk_lt_mk.mpr hlt)
    have ha_eq : l[a]! = l.get ⟨a, ha⟩ := by simp [ha]
    have hb_eq : l[b]! = l.get ⟨b, hb⟩ := by simp [hb]
    rw [ha_eq, hb_eq]
    exact hge
  · subst heq; exact le_refl _

/-- In `(List.range n).map f`, the element at index `i` (with `i < n`) is `f i`. -/
lemma getElem?_map_range {α : Type} (f : Nat → α) (n i : Nat) (h : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  simp [List.getElem?_map, List.getElem?_range, h]

/-- `getElem!` version of `getElem?_map_range`:
`((List.range n).map f)[i]! = f i` when `i < n`. -/
lemma getElem!_range_map_eq {α : Type} [Inhabited α] (f : Nat → α) (n i : Nat) (hi : i < n) :
    ((List.range n).map f)[i]! = f i := by
  simp [List.getElem?_map, List.getElem?_range hi]

/-- The length of `(List.range n).map f` is exactly `n`. -/
lemma length_map_range {α : Type} (f : Nat → α) (n : Nat) : ((List.range n).map f).length = n := by
  simp

/-! ### `getElem!` with `cons` -/

/-- For a non-zero index, `(x :: l)[i]!` reduces to `l[i-1]!`.
Useful when the index is known to be at least `1`. -/
lemma getElem!_cons_sub {α : Type} [Inhabited α] (x : α) (l : List α) (i : Nat) (h : 1 ≤ i) :
    (x :: l)[i]! = l[i-1]! := by
  have hi : i = (i-1) + 1 := by omega
  nth_rw 1 [hi]
  rw [List.getElem!_cons_succ]

/-! ### `getElem!` with `append` -/

/-- `getElem!` on an appended list: `(l₁ ++ l₂)[i]!` decomposes into
either `l₁[i]!` (if `i < l₁.length`) or `l₂[i - l₁.length]!` (otherwise).
This is the `getElem!` counterpart of `List.getElem?_append`. -/
lemma getElem!_append {α : Type} [Inhabited α] (l₁ l₂ : List α) (i : Nat) :
    (l₁ ++ l₂)[i]! = (if i < l₁.length then l₁[i]! else l₂[i - l₁.length]!) := by
  simp only [LawfulGetElem.getElem!_def, List.getElem?_append]
  by_cases h : i < l₁.length
  · simp [h]
  · simp [h]

/-! ### Accessing elements of a reversed cons -/

/-- The last element of a reversed cons `(a :: L).reverse` (at index `L.length`) is the head `a`. -/
lemma getElem_reverse_cons_last {α : Type} [Inhabited α] (L : List α) (a : α) :
    ((a :: L).reverse)[L.length]! = a := by
  have hrev : (a :: L).reverse = L.reverse ++ [a] := by simp
  rw [hrev, getElem!_append]
  have hlen : ¬ L.length < L.reverse.length := by
    simpa [List.length_reverse] using Nat.not_lt.mpr (le_refl L.length)
  rw [if_neg hlen]
  simp

/-- For a non-last index `i < L.length`, the element at index `i` of `(a :: L).reverse`
equals the element at index `i` of `L.reverse`. -/
lemma getElem_reverse_cons_lt {α : Type} [Inhabited α] (L : List α) (a : α) (i : Nat)
    (h : i < L.length) :
    ((a :: L).reverse)[i]! = L.reverse[i]! := by
  have hrev : (a :: L).reverse = L.reverse ++ [a] := by simp
  rw [hrev, getElem!_append]
  have hi_rev : i < L.reverse.length := by
    simpa [List.length_reverse] using h
  rw [if_pos hi_rev]

/-- Building a list by `cons` and `reverse` preserves an invariant indexed by position:
if `acc.reverse` agrees with `f` on each index `i < acc.length`, and `x = f acc.length`,
then `(x :: acc).reverse` agrees with `f` on each index `i < (x :: acc).length`.
This is a key lemma for accumulator-based reverse list construction. -/
lemma reverse_cons_invariant {α : Type} [Inhabited α] (f : Nat → α) (x : α) (acc : List α)
    (hpref : ∀ i, i < acc.length → acc.reverse[i]! = f i)
    (hx : x = f acc.length) :
    ∀ i, i < (x :: acc).length → ((x :: acc).reverse)[i]! = f i := by
  intro i hi
  have hrev : (x :: acc).reverse = acc.reverse ++ [x] := by simp
  rw [hrev, getElem!_append]
  by_cases hcase : i < acc.reverse.length
  · rw [if_pos hcase]
    have h_i_acc : i < acc.length := by
      simpa [List.length_reverse] using hcase
    exact hpref i h_i_acc
  · rw [if_neg hcase]
    have h_not_lt : ¬ i < acc.length := by
      simpa [List.length_reverse] using hcase
    have hi_bound : i < acc.length + 1 := by
      simpa [List.length_cons] using hi
    have h_eq : i = acc.length := by omega
    subst h_eq
    simp [hx, LawfulGetElem.getElem!_def, List.length_reverse]

/-! ### `getD` with `append` -/

/-- `(pref ++ [x]).getD pref.length d = x`: accessing the element at
the index equal to `pref.length` in `pref ++ [x]` returns `x`.
This is a specialized form of `List.getD_append_right` for the common
case of a singleton suffix. -/
lemma getD_append_right_singleton {α : Type} (pref : List α) (x : α) (d : α) :
    (pref ++ [x]).getD pref.length d = x := by
  rw [List.getD_append_right pref [x] d pref.length (le_refl _)]
  simp

/-- If `p` has length `len`, then `(p ++ t).getD (len + i) d = t.getD i d`.
This generalizes `List.getD_append_right` by rewriting the index using a length hypothesis. -/
lemma getD_append_of_length_eq {α : Type} (p t : List α) (d : α) (len i : Nat)
    (hp_len : p.length = len) :
    (p ++ t).getD (len + i) d = t.getD i d := by
  have hle : p.length ≤ len + i := by
    rw [hp_len]; omega
  rw [List.getD_append_right p t d (len + i) hle, hp_len, Nat.add_sub_cancel_left]

/-- A QuickCheck-friendly corollary of `getElem?_map_range`: using `List.all` with `decide`
to assert that every index `i` in `range n` satisfies `((range n).map f)[i]? = some (f i)`.
This always holds and is useful for finite postcondition verification. -/
lemma all_getElem?_map_range_eq {α : Type} [DecidableEq α] (f : Nat → α) (n : Nat) :
    ((List.range n).all (fun i =>
      decide (((List.range n).map f)[i]? = some (f i)))) = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  simpa using getElem?_map_range f n i hi

/-! ### `get` with `append` -/

/-- In `as ++ c :: bs`, the length of `as` is strictly less than the length of the whole list.
This provides the index-bound proof term needed for `get_append_left_length`. -/
lemma length_lt_append_cons {α : Type _} (as bs : List α) (c : α) :
    as.length < (as ++ c :: bs).length := by
  rw [List.length_append]
  have hpos : 0 < (c :: bs).length := by simp
  omega

/-- In `as ++ c :: bs`, the element at the boundary index `as.length` is exactly `c`.
This is a specialized form of `List.getElem_append_right` for the common case where
the index is exactly at the split between the two lists.
Prefer `length_lt_append_cons` for the proof of the index-bound hypothesis `h`. -/
lemma get_append_left_length {α : Type _} (as bs : List α) (c : α)
    (h : as.length < (as ++ c :: bs).length) :
    (as ++ c :: bs).get ⟨as.length, h⟩ = c := by
  induction' as with a as' ih generalizing bs
  · simp
  · simp [ih]

/-- The last element of `l ++ [x]` is `x`, accessed via `get` using the index `l.length`.
This is the `get` counterpart of `getD_append_right_singleton`. -/
lemma get_append_singleton_right {α : Type} (l : List α) (x : α)
    (h : l.length < (l ++ [x]).length) :
    (l ++ [x]).get ⟨l.length, h⟩ = x := by
  simp

/-- An index `k` into `l ++ [x]` is either in `l` (`k < l.length`) or points to `x` itself
(`k = l.length`). Useful for case-splitting when reasoning about appending a singleton. -/
lemma index_lt_append_singleton {α : Type} (l : List α) (x : α) (k : Nat)
    (hk : k < (l ++ [x]).length) : k < l.length ∨ k = l.length := by
  have h_len : (l ++ [x]).length = l.length + 1 := by simp
  omega

/-! ### Range decomposition -/

/-- `List.range (n + 1)` equals `List.range n` with `n` appended at the end.
This is an alternative decomposition to `List.range_succ`, which expresses
`range (n + 1)` as `0 :: (range n).map (· + 1)`. -/
lemma range_succ_append (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  induction' n with k ih
  · rfl
  · simp [List.range_succ, ih]

/-- Mapping `f` over `List.range (n + 1)` equals mapping over `List.range n` with `f n` appended.
Useful for decomposing `(List.range (n+1)).map f` into the first `n` elements plus the last. -/
lemma map_range_succ_append (n : Nat) (f : Nat → α) : (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
  rw [range_succ_append, List.map_append, List.map_singleton]

/-- If `j < n`, then `f j` is in the result of mapping `f` over `List.range n`. -/
lemma mem_map_range {α : Type u} (f : Nat → α) (n j : Nat) (h : j < n) : f j ∈ (List.range n).map f :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩

/-- If `n > 0`, then `List.range n` is not empty. -/
lemma range_ne_nil_of_pos {n : Nat} (h : 0 < n) : List.range n ≠ [] := by
  intro h_eq
  have h0_mem : 0 ∈ List.range n := by
    rw [List.mem_range]; exact h
  rw [h_eq] at h0_mem
  simp at h0_mem

/-! ### Inclusive range — list of indices from `l` to `r` inclusive -/

/-- List of indices from `l` to `r` inclusive: `[l, l+1, …, r]`.
When `l > r`, returns the empty list (because `Nat` subtraction saturates at zero). -/
def inclusiveRange (l r : Nat) : List Nat :=
  (List.range (r + 1 - l)).map (fun d => l + d)

lemma inclusiveRange_empty_of_gt {l r : Nat} (h : r < l) : inclusiveRange l r = [] := by
  have hle : r + 1 ≤ l := Nat.succ_le_of_lt h
  have hsub : r + 1 - l = 0 := Nat.sub_eq_zero_of_le hle
  simp [inclusiveRange, hsub]

lemma inclusiveRange_self (l : Nat) : inclusiveRange l l = [l] := by
  dsimp [inclusiveRange]
  have hsub : l + 1 - l = 1 := by omega
  have hrange : List.range 1 = [0] := by decide
  simp [hsub, hrange]

/-- Membership in `inclusiveRange l r`: `x` belongs to `[l, l+1, …, r]` iff `l ≤ x ≤ r`.
When `l > r`, both sides are false (the list is empty and no `x` satisfies `l ≤ x ≤ r`). -/
lemma mem_inclusiveRange_iff {l r x : Nat} : x ∈ inclusiveRange l r ↔ l ≤ x ∧ x ≤ r := by
  dsimp [inclusiveRange]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
    rw [List.mem_range] at hd
    constructor
    · exact Nat.le_add_right l d
    · omega
  · intro ⟨hlx, hxr⟩
    have hsub : x - l < r + 1 - l := by omega
    have hsum : l + (x - l) = x := Nat.add_sub_cancel' hlx
    exact List.mem_map.mpr ⟨x - l, by rw [List.mem_range]; exact hsub, hsum⟩

/-- `inclusiveRange l r` has no duplicates — each index appears exactly once. -/
lemma nodup_inclusiveRange {l r : Nat} : (inclusiveRange l r).Nodup := by
  dsimp [inclusiveRange]
  apply List.Nodup.map
  · intro a b h
    exact Nat.add_left_cancel h
  · exact List.nodup_range _

/-! ### `getElem?` convenience lemmas -/

/-- When `i` is within bounds, `l[i]?` returns `some (l[i])`.
This is the forward direction of `List.getElem?_eq_some_iff`. -/
lemma getElem?_eq_some_of_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    l[i]? = some (l[i]) := by
  rw [List.getElem?_eq_some_iff]
  exact ⟨h, rfl⟩

/-- If `l[i]? = some a`, then `i < l.length`. This is the partial converse of
`getElem?_eq_some_of_lt`, extracting just the bounds proof from `getElem?_eq_some_iff`. -/
lemma getElem?_eq_some_imp_lt {α : Type u} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨h_lt, _⟩
  exact h_lt

/-- If `l[i] = a` and `i` is within bounds, then `l[i]? = some a`.
This generalizes `getElem?_eq_some_of_lt` to the case where the element
is known to equal `a` (rather than trivially `l[i]`). -/
lemma getElem?_eq_some_of_getElem_eq {α : Type} {l : List α} {i : Nat} {a : α}
    (h_bound : i < l.length) (h_eq : l[i] = a) : l[i]? = some a := by
  rw [List.getElem?_eq_some_iff]
  exact ⟨h_bound, h_eq⟩

/-! ### `getElem!` on `map` -/

/-- `(l.map f)[i]? = some (f (l[i]))` when `i` is in bounds.
This is the `getElem?` counterpart of `getElem!_map`. -/
lemma getElem?_map_eq {α β : Type} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
    (l.map f)[i]? = some (f (l[i])) := by
  have hlen : i < (l.map f).length := by
    rw [List.length_map]
    exact h
  rw [List.getElem?_eq_getElem hlen, List.getElem_map]

/-- Convenience wrapper around `List.getElem_map` that accepts a proof about the
*original* list's length instead of the mapped list's length. This is the common
case when you know `i < l.length` and want to evaluate `(l.map f).get ⟨i, ...⟩`. -/
lemma getElem_map_eq {α β : Type} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    (l.map f).get ⟨i, by simpa [List.length_map] using hi⟩ = f (l.get ⟨i, hi⟩) := by
  have hi' : i < (l.map f).length := by
    simpa [List.length_map] using hi
  exact List.getElem_map f (l := l) (i := i) (h := hi')


/-- If `l[idx]? = some x`, then `(l.map f)[idx]? = some (f x)`.
This is useful when the index result is already known rather than using an index-bound hypothesis. -/
lemma getElem?_map_eq_some {α β : Type u} (f : α → β) (l : List α) (idx : Nat) (x : α)
    (h : l[idx]? = some x) : (l.map f)[idx]? = some (f x) := by
  simp [List.getElem?_map, h]

/-- `getElem!` commutes with `map` for valid indices: `(l.map f)[i]! = f (l[i]!)`.
This is the `getElem!` counterpart of `List.getElem?_map`. -/
lemma getElem!_map [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) : (l.map f)[i]! = f (l[i]!) := by
  have hmap : i < (l.map f).length := by simpa [List.length_map] using h
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hmap, List.getElem?_eq_getElem h]
  simp

/-- `map` preserves `getElem!` for indices known to be in `List.range l.length`.
Useful when the index bound is expressed as `mem_range` rather than `i < l.length`. -/
lemma getElem!_map_range [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat)
    (h : i ∈ List.range l.length) : (l.map f)[i]! = f (l[i]!) := by
  rw [List.mem_range] at h
  exact getElem!_map f l i h

/-- `getElem!` commutes with `map` of a projection to the second component of a pair:
`(l.map (fun p => f p.2))[i]! = f (l[i]!).2` when `i` is in bounds. -/
lemma getElem!_map_snd [Inhabited α] [Inhabited β] [Inhabited γ] (f : β → γ) (l : List (α × β)) (i : Nat)
    (h : i < l.length) : (l.map (fun p => f p.2))[i]! = f (l[i]!).2 := by
  calc
    (l.map (fun p => f p.2))[i]! = (fun p => f p.2) (l[i]!) := getElem!_map (fun p => f p.2) l i h
    _ = f (l[i]!).2 := rfl

/-! ### `getElem?` and `getElem!` on `ofFn` -/

/-- If `i < n`, then `(List.ofFn f)[i]! = f ⟨i, h⟩`.
This bridges `List.ofFn` indexing with `Fin`-based function access
using the unchecked `getElem!` notation. -/
lemma getElem!_ofFn_eq {α : Type} {n : Nat} [Inhabited α] (f : Fin n → α) (i : Nat) (h : i < n) :
    (List.ofFn f)[i]! = f ⟨i, h⟩ := by
  have hget! : (List.ofFn f)[i]! = ((List.ofFn f)[i]?).getD default := by simp
  have hget? : ((List.ofFn f)[i]?).getD default = f ⟨i, h⟩ := by
    simp [List.getElem?_ofFn, h]
  rw [hget!, hget?]

/-- If `i < n`, then `(List.ofFn f)[i]? = some (f ⟨i, hi⟩)`.
This bridges `List.ofFn` indexing with `Fin`-based function access
using the safe `getElem?` (Option-returning) notation. -/
lemma getElem?_ofFn_eq_some {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) :
    (List.ofFn f)[i]? = some (f ⟨i, hi⟩) := by
  rw [List.getElem?_ofFn]
  simp [hi]

/-- If `i < n`, then `(List.ofFn f)[i]?.iget = f ⟨i, hi⟩`.
This bridges `List.ofFn` indexing with `Fin`-based function access
using the `Option.iget` notation (which requires `Inhabited α`). -/
lemma getElem?_ofFn_iget_eq {α : Type} {n : Nat} [Inhabited α] (f : Fin n → α) (i : Nat) (hi : i < n) :
    (List.ofFn f)[i]?.iget = f ⟨i, hi⟩ := by
  simp [hi]

/-- If `i < n`, then `(List.ofFn f).getD i d = f ⟨i, h⟩`.
This is the `getD` variant of `getElem?_ofFn_eq_some` and `getElem!_ofFn_eq`,
bridging `List.ofFn` with `getD`-based element access. -/
lemma getD_ofFn_eq {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [List.getD, List.getElem?_ofFn]
  simp [h]

/-- If `i : Fin n`, then `(List.ofFn f).getD i.val d = f i`.
This is the `Fin`-based variant of `getD_ofFn_eq`, avoiding the need to pass an explicit
bound proof. Useful when working with `List.ofFn` results indexed by `Fin n`. -/
lemma getD_ofFn_val {n : Nat} {α : Type} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD (i.val) d = f i := by
  have h := getD_ofFn_eq f (i.val) i.2 d
  simpa [Fin.eta] using h

/-- For a 2D array constructed via nested `List.ofFn`, accessing `[i.val][j.val]` with
`getD` returns `f i j`. This is the 2D generalization of `getD_ofFn_val`. -/
lemma getD_ofFn_ofFn_getD {n : Nat} {α : Type} (f : Fin n → Fin n → α) (i j : Fin n) (d : α) (row_d : List α) :
    ((List.ofFn (fun (i' : Fin n) => List.ofFn (f i'))).getD i.val row_d).getD j.val d = f i j := by
  have hrow : (List.ofFn (fun (i' : Fin n) => List.ofFn (f i'))).getD i.val row_d = List.ofFn (f i) := by
    simpa using getD_ofFn_val (fun (i' : Fin n) => List.ofFn (f i')) i row_d
  rw [hrow]
  simpa using getD_ofFn_val (f i) j d

/-- If `i < n`, then `i` is a valid index into `List.ofFn f`.
This bridges the `Fin n` bound into a list-length bound, useful when
converting `Fin`-based indexing proofs into list indexing proofs. -/
lemma lt_length_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < n) :
    i < (List.ofFn f).length := by
  simpa [List.length_ofFn] using h

/-- If `i < n`, then `(List.ofFn (λ j : Fin n => f j.val))[i]? = some (f i)`.
This is the `Nat → α` variant of `getElem?_ofFn_eq_some`, convenient when
the generating function is defined on all `Nat` rather than on `Fin n`. -/
lemma getElem?_ofFn_val {α : Type _} (f : Nat → α) (n i : Nat) (h : i < n) :
    ((List.ofFn (λ (j : Fin n) => f j.val))[i]?) = some (f i) := by
  rw [List.getElem?_ofFn]
  simp [h]

/-- If `i < n`, then `(List.ofFn (λ j : Fin n => f j.val))[i]! = f i`.
This is the `getElem!` variant of `getElem?_ofFn_val`, bridging `List.ofFn` with
`Nat → α` functions when using the unchecked `getElem!` notation. -/
lemma getElem!_ofFn_val {α : Type _} [Inhabited α] (f : Nat → α) (n i : Nat) (h : i < n) :
    ((List.ofFn (λ (j : Fin n) => f j.val))[i]!) = f i := by
  have hget : ((List.ofFn (λ (j : Fin n) => f j.val))[i]?) = some (f i) :=
    getElem?_ofFn_val f n i h
  simp [hget]

/-! ### `getElem!` and `get` -/

/-- `l[i]! = l.get ⟨i, hi⟩` when `i < l.length`.
This bridges the `getElem!` notation (which uses `default` for out-of-bounds) with `get`
(which uses a proof of `i < l.length`). -/
lemma getElem!_eq_get_of_lt {α : Type} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  have h_get? : l[i]? = some (l.get ⟨i, hi⟩) := by
    simp [hi]
  simp [h_get?]

/-! ### `getElem?` / `getElem!` bridge -/

/-- When `i` is in bounds, `(l[i]?).get! = l[i]!`.
Bridges the safe `getElem?` (returns `Option α`) combined with `Option.get!` (which panics
on `none`) to the direct `getElem!` (which uses `Inhabited.default` for out‑of‑bounds). -/
lemma getElem?_get!_eq_getElem! {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    (l[i]?).get! = l[i]! := by
  have h1 : l[i]? = some (l[i]) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨h, rfl⟩
  simp [h1, h]

/-- The quantifier `∀ i < l.length, P i ((l[i]?).get!)` is equivalent to
`∀ i < l.length, P i (l[i]!)`.  Useful when a spec uses one form and an implementation
uses the other.  Relies on `getElem?_get!_eq_getElem!` for the per‑index equality. -/
lemma forall_lt_length_getElem_iff {α : Type} [Inhabited α] {l : List α} {P : Nat → α → Prop} :
    (∀ i, i < l.length → P i ((l[i]?).get!)) ↔ (∀ i, i < l.length → P i (l[i]!)) := by
  constructor
  · intro h_i i hi
    have hget : (l[i]?).get! = l[i]! := getElem?_get!_eq_getElem! l i hi
    simpa [hget] using h_i i hi
  · intro h_i i hi
    have hget : (l[i]?).get! = l[i]! := getElem?_get!_eq_getElem! l i hi
    simpa [hget] using h_i i hi

/-! ### Membership and indexing bridge -/

/-- If `l[i]? = some x`, then `x ∈ l`. This bridges `getElem?`-based access
to plain list membership. -/
lemma mem_of_getElem?_eq_some {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : x ∈ l := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hget⟩
  rw [← hget]
  exact List.get_mem _ _

/-- `x ∈ l` if and only if there exists an index `i < l.length` such that
`l[i]? = some x`. This bridges list membership to indexed (`getElem?`) access. -/
lemma mem_iff_exists_index_getElem? {α : Type} {l : List α} {x : α} :
    x ∈ l ↔ ∃ i, i < l.length ∧ l[i]? = some x := by
  constructor
  · intro h
    rcases List.mem_iff_get.mp h with ⟨i, hi⟩
    refine ⟨i.val, i.isLt, ?_⟩
    rw [List.getElem?_eq_some_iff]
    exact ⟨i.isLt, hi⟩
  · intro ⟨i, hi, h⟩
    exact mem_of_getElem?_eq_some h

/-- `(∀ x ∈ l, P x)` is equivalent to `(∀ i < l.length, P (l.get ⟨i, hi⟩))`.
This bridges membership-based quantification and index-based quantification over a list,
using the `get` API with explicit `Nat`+proof indexing (the `getElem` counterpart
is mathlib's `forall_mem_iff_getElem`). -/
lemma forall_mem_iff_forall_get {α : Type u} (l : List α) (P : α → Prop) :
    (∀ x ∈ l, P x) ↔ (∀ i, ∀ hi : i < l.length, P (l.get ⟨i, hi⟩)) := by
  constructor
  · intro h i hi; exact h (l.get ⟨i, hi⟩) (List.get_mem _ _)
  · intro h x hx; rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩; exact h i.val i.isLt

/-- If for every position `i < xs.length`, the optional lookup `xs[i]?` yields a value
from `alphabet`, then every element of `xs` is in `alphabet`.

This bridges the `getElem?`-based positional characterization of list membership
("every position's value is from `alphabet`") to the direct element-wise membership
("∀ a ∈ xs, a ∈ alphabet"). -/
lemma of_forall_getElem?_mem {xs : List α} {alphabet : List α}
    (h : ∀ (i : Nat), i < xs.length → ∃ a ∈ alphabet, xs[i]? = some a) :
    ∀ a ∈ xs, a ∈ alphabet := by
  intro a ha
  rcases List.mem_iff_get.mp ha with ⟨i, hi⟩
  let n := (i : Nat)
  have hn_lt : n < xs.length := i.2
  have h_get?_val : xs[n]? = some a := by
    calc
      xs[n]? = some (xs[n]) := List.getElem?_eq_getElem hn_lt
      _ = some a := by simpa using hi
  rcases h n hn_lt with ⟨a', ha'_in_alphabet, h_get'⟩
  have h_eq : a = a' := by
    have : some a = some a' := by rw [← h_get?_val, h_get']
    simpa using this
  rw [h_eq]
  exact ha'_in_alphabet

/-- If `a` is not in `l`, then for any in-bounds index `i`, `l[i]?` is never `some a`.
This bridges non-membership (`a ∉ l`) to the `getElem?`-based positional
characterization: no position returns `some a`. -/
lemma forall_getElem?_ne_some_of_not_mem {l : List α} {a : α} (h : a ∉ l) :
    ∀ i, i < l.length → l[i]? ≠ some a := by
  intro i hi h_eq
  rw [List.getElem?_eq_some_iff] at h_eq
  rcases h_eq with ⟨_, h_arr_eq⟩
  apply h
  rw [← h_arr_eq]
  exact List.getElem_mem hi

/-! ### Membership and Reverse -/

/-- `List.Forall` distributes over `++`:
`(l₁ ++ l₂).Forall p ↔ l₁.Forall p ∧ l₂.Forall p`. -/
lemma forall_append {α : Type} {p : α → Prop} {l₁ l₂ : List α} :
    (l₁ ++ l₂).Forall p ↔ l₁.Forall p ∧ l₂.Forall p := by
  induction l₁ with
  | nil => simp
  | cons h t ih =>
    simp [ih, and_assoc]

/-- `List.Forall` trivially holds for the empty list. -/

lemma forall_nil {α : Type} (p : α → Prop) : List.Forall p [] := by
  simp

/-- If a predicate `P` holds for all elements of `l`, it also holds for all elements
of `l.reverse`, since `reverse` preserves the set of elements. -/
lemma forall_mem_reverse {α : Type u} {P : α → Prop} {l : List α} (h : ∀ a ∈ l, P a) :
    ∀ a ∈ l.reverse, P a := by
  simpa [List.mem_reverse] using h

/-- If an element is in the reverse of a filtered list, it satisfies the filter predicate. -/
lemma mem_reverse_filter {α : Type u} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ (l.filter p).reverse) : p x := by
  rcases List.mem_reverse.mp hx with hx'
  exact (List.mem_filter.mp hx').2

/-! ### `List.Forall` ↔ membership conversions -/

/-- Extract `P a` from `List.Forall P l` given that `a ∈ l`. -/
lemma forall_of_mem {α : Type} {P : α → Prop} {l : List α} {a : α}
    (h : List.Forall P l) (ha : a ∈ l) : P a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      rcases ((List.forall_cons P x xs).mp h) with ⟨hx, hxs⟩
      rcases List.mem_cons.mp ha with (rfl | ha')
      · exact hx
      · exact ih hxs ha'

/-- Convert `∀ a, a ∈ l → P a` to `List.Forall P l`. -/
lemma forall_of_forall_mem {α : Type} {P : α → Prop} {l : List α}
    (h : ∀ a, a ∈ l → P a) : List.Forall P l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.forall_cons]
      exact ⟨h x (by simp), ih (fun a ha => h a (by simp [ha]))⟩

/-- If `l₁` is a sublist of `l₂` and every element of `l₂` satisfies `P`,
then every element of `l₁` also satisfies `P`.
In other words, `Forall P` propagates downward through `Sublist`. -/
lemma forall_of_sublist {α : Type} {P : α → Prop} {l₁ l₂ : List α} (h : l₁ <+ l₂) (hP : Forall P l₂) :
    Forall P l₁ := by
  induction h with
  | slnil => exact hP
  | cons _ _ ih =>
    rcases (forall_cons P _ _).mp hP with ⟨_, hP'⟩
    exact ih hP'
  | cons₂ _ _ ih =>
    rcases (forall_cons P _ _).mp hP with ⟨ha, hP'⟩
    apply (forall_cons P _ _).mpr
    exact ⟨ha, ih hP'⟩


end List

namespace List

/-! # Lemmas about `List.getD`

`getD` is a safe accessor that returns the element at index `i` if it's in-bounds,
or a default value `d` otherwise.
-/

/-- If `l = l1 ++ a :: l2`, then `l.getD l1.length d = a`.
This lemma delegates to `getD_append` when the index equals the length of the first segment. -/
lemma getD_append_singleton {α : Type _} (l1 l2 : List α) (a d : α) :
    (l1 ++ a :: l2).getD l1.length d = a := by
  induction l1 with
  | nil => simp
  | cons h t ih => simp [ih]

/-- If `lst[pos]? = some a`, then `lst.getD pos d = a` for any default `d`.
This is the bridge between `getElem?` (optional access) and `getD` (defaulted access). -/
lemma getD_of_getElem?_eq_some {α : Type} (lst : List α) (pos : Nat) (d a : α)
    (h : lst[pos]? = some a) : lst.getD pos d = a := by
  unfold List.getD
  simp [h]

/-! ### `getNat`: safe indexing with default 0 for `List Nat` -/

/-- Safe list indexing returning `0` for out-of-bounds. Equivalent to `l.getD n 0`.
Useful for DP table lookups where missing values default to 0. -/
def getNat (l : List Nat) (n : Nat) : Nat := l.getD n 0

/-! ### `getD_map_eq_map_getD` — `getD` on a mapped list with flexible defaults

This generalizes `List.getD_map` from mathlib, which requires the default on the
mapped side to be `f d`. Here, the default `dflt` on the mapped side only needs to
equal `f d` (the result of applying `f` to the default on the original side). -/

/-- `(l.map f).getD i dflt = f (l.getD i d)` provided `f d = dflt`.
This generalizes mathlib's `List.getD_map` by allowing the default on the mapped
side to be different from `f d`, as long as they are equal.
For the case where `i` is in-bounds, the defaults are irrelevant; when `i` is
out-of-bounds, both sides evaluate to `f d`. -/
lemma getD_map_eq_map_getD {α β : Type} (f : α → β) (dflt : β) (d : α) (l : List α) (i : Nat)
    (hd : f d = dflt) : (l.map f).getD i dflt = f (l.getD i d) := by
  have h := List.getD_map l d (n := i) f
  simpa [hd] using h

/-- If `x` is a member of a list, there exists an in-bounds index where `getD` returns `x`.
This bridges `List.Mem` to the `getD` accessor: membership implies the element can be
retrieved at some valid index via `getD` with any default value. -/
lemma mem_implies_exists_getD_eq {α : Type} {arr : List α} (x : α) (def_val : α) (h_mem : x ∈ arr) :
    ∃ i, i < arr.length ∧ arr.getD i def_val = x := by
  rcases List.mem_iff_get.1 h_mem with ⟨⟨i, hi⟩, rfl⟩
  refine ⟨i, hi, ?_⟩
  rw [List.getD_eq_getElem _ def_val hi]
  rfl

end List


namespace List

/-! ### `checkPairWith` — test a binary predicate on two list elements by index -/

/-- Check whether `i < j` and both `xs[i]?` and `xs[j]?` are `some` values
satisfying the binary boolean predicate `p`. Returns `false` if either index
is out of bounds or `i ≥ j`. -/
def checkPairWith {α : Type} (p : α → α → Bool) (xs : List α) (i j : Nat) : Bool :=
  if i < j then
    match xs[i]?, xs[j]? with
    | some x, some y => p x y
    | _, _ => false
  else false

end List

namespace List

/-! ### Properties of `getD` -/

/-- `getD` on an empty list returns the default value for any index. -/

lemma getD_nil_eq_default {α : Type} (i : Nat) (d : α) : ([] : List α).getD i d = d := by
  simp

/-- If the index is within bounds, `getD` retrieves the element at that position. -/
lemma getD_eq_get_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l[i]?).getD d = l.get ⟨i, h⟩ := by
  have h_some : l[i]? = some (l.get ⟨i, h⟩) :=
    (List.getElem?_eq_some_iff).mpr ⟨h, rfl⟩
  rw [h_some]
  simp

/-- When the index is within bounds, the default value passed to `getD` does not matter.
`l.getD i d1 = l.getD i d2` whenever `i < l.length`.
Note that `l.getD i d` is equivalent to `(l[i]?).getD d`. -/
lemma getD_irrelevant {α : Type u} (l : List α) (i : Nat) (d1 d2 : α) (h : i < l.length) :
    l.getD i d1 = l.getD i d2 := by
  rw [getD_eq_getElem _ d1 h, getD_eq_getElem _ d2 h]

/-- If the index is beyond the list's length, `getD` returns the default value. -/
lemma getD_eq_of_length_le {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    (l[i]?).getD d = d := by
  have h_none : l[i]? = none := List.getElem?_eq_none (by omega)
  rw [h_none]
  simp

/-- If the index is within bounds, `l.getD i d` is an element of `l`.
The default value `d` is irrelevant — when `i < l.length`, `getD i d`
always returns a genuine element from the list. -/
lemma getD_mem_of_lt_length {α : Type u} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem l d h]
  exact List.getElem_mem h

/-- `(l.drop i).getD 0 d = l.getD i d`: accessing the first element of a dropped list
via `getD` is the same as accessing the `i`-th element of the original list.
This is a fundamental identity connecting `drop` and `getD`. -/
lemma getD_drop_zero_eq_getD {α : Type u} (l : List α) (i : Nat) (d : α) :
    (l.drop i).getD 0 d = l.getD i d := by
  induction l generalizing i with
  | nil => simp
  | cons h t ih =>
    cases i with
    | zero => simp
    | succ i => simp [ih i]

/-- If `List.drop i l = a :: t`, then `l.getD i d = a`. -/
lemma getD_eq_of_drop_eq_cons {α : Type u} (l : List α) (a : α) (t : List α) (i : Nat) (d : α)
    (h_drop : l.drop i = a :: t) : l.getD i d = a := by
  rw [← getD_drop_zero_eq_getD l i d, h_drop]
  simp

/-- Mapping `getD i d` over `range l.length` recovers the original list.
This holds because for every `i < l.length`, `getD i d` returns the `i`-th element
regardless of the default value `d`. -/
lemma map_getD_range_eq_self {α : Type} (l : List α) (d : α) :
    List.map (fun i => l.getD i d) (List.range l.length) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa [List.range_succ_eq_map, List.map_map] using congrArg (x :: ·) ih

/-- Sum of `values.getD i 0` over `i ∈ range (values.length)` equals
`values.foldl (+) 0`. -/
lemma sum_map_getD_range_eq_foldl (values : List Nat) :
    List.foldl (· + ·) 0 (List.map (fun i => values.getD i 0) (List.range (values.length))) =
    values.foldl (· + ·) 0 := by
  rw [map_getD_range_eq_self values 0]

/-- When `i` is in bounds, `l[(l[i]?).getD d]?` equals `l[l[i]]?`.
That is, resolving `getD` then looking up again is the same as direct double-indexing
when both indices are valid. This is useful when a list is used as a self-index lookup table
and the elements serve as indices into the same list. -/
lemma getElem?_getD_getElem_eq (l : List Nat) (i d : Nat) (hi : i < l.length) :
    l[(l[i]?).getD d]? = l[l[i]]? := by
  have h : l[i]? = some (l[i]) := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  simp [h]

/-- Accessing the successor index on a cons drops the head:
`(x :: xs).getD (i + 1) d = xs.getD i d`. -/

lemma getD_succ_cons {α : Type} (x : α) (xs : List α) (i : Nat) (d : α) :
    (x :: xs).getD (i + 1) d = xs.getD i d := by
  simp [List.getD]

/-- Accessing index 0 on a cons returns the head:
`(x :: xs).getD 0 d = x`. -/

lemma getD_zero_cons {α : Type} (x : α) (xs : List α) (d : α) :
    (x :: xs).getD 0 d = x := by
  simp [List.getD]

/-- When the index is within bounds, `getD` on a mapped list equals the function applied
to `getD` on the original list, regardless of the default values chosen.
This generalizes `List.getD_map` which requires the default on the mapped side to be `f d`. -/
lemma getD_map_eq_of_lt {α β : Type _} (l : List α) (f : α → β) (i : Nat) (h : i < l.length) (d : β) (d' : α) :
    (l.map f).getD i d = f (l.getD i d') := by
  have hlen : i < (l.map f).length := by
    rw [List.length_map]
    exact h
  rw [List.getD_eq_getElem (l.map f) d hlen, List.getD_eq_getElem l d' h, List.getElem_map]

/-- When the index is within bounds, `getD` on a `mapIdx` list equals the function applied
to the index and the `getD` of the original list, regardless of the default values chosen. -/
lemma getD_mapIdx_eq_of_lt {α β : Type} (l : List α) (f : Nat → α → β) (j : Nat) (h : j < l.length) (d : β) (d' : α) :
    (l.mapIdx f).getD j d = f j (l.getD j d') := by
  have hlen : j < (l.mapIdx f).length := by
    rw [List.length_mapIdx]
    exact h
  rw [List.getD_eq_getElem (l.mapIdx f) d hlen, List.getElem_mapIdx, ← List.getD_eq_getElem l d' h]

/-- The first element of `List.scanl f a l` accessed via `getD` is always `a`,
since `scanl` starts with the initial accumulator. -/
lemma getD_scanl_head {α β : Type} (f : α → β → α) (a : α) (l : List β) (d : α) :
    (List.scanl f a l).getD 0 d = a := by
  simp [List.scanl]

/-- If a replicated value `x` satisfies `x < bound`, then `getD` at any in-bounds
index on `replicate n x` also satisfies the inequality. -/
lemma getD_replicate_lt {α : Type} [LT α] {x d : α} {n k : ℕ} {bound : α}
    (hx : x < bound) (hk : k < n) : (replicate n x).getD k d < bound := by
  rw [getD_replicate (x := x) (y := d) hk]
  exact hx

end List

namespace List

/-! ### `Sorted` from universal relation -/

/-- If a relation `R` holds universally (for all `x, y`), then any list is `Sorted` by `R`.
This is the `List` analogue of `Set.pairwise_of_forall`. -/
lemma sorted_of_constant_rel {α : Type} (R : α → α → Prop) (l : List α) (h : ∀ x y, R x y) :
    l.Sorted R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.Pairwise.cons ?_ ih
    intro a' _ha'
    exact h a a'

/-! ### `getD` and `Pairwise` — connecting indexed and structural order -/

/-- Index-wise `getD` ordering implies `List.Pairwise` for the same relation.
Useful for converting between indexed and structural order properties. -/
lemma pairwise_of_getD_ordered {α : Type} [Inhabited α] {R : α → α → Prop} {xs : List α} {d : α}
    (h_idx : ∀ i j, i < j → i < xs.length → j < xs.length → R ((xs[i]?).getD d) ((xs[j]?).getD d)) :
    List.Pairwise R xs := by
  rw [List.pairwise_iff_get]
  intro i_val j_val hlt
  have hi_lt : (i_val : Nat) < xs.length := i_val.2
  have hj_lt : (j_val : Nat) < xs.length := j_val.2
  have hlt_val : (i_val : Nat) < (j_val : Nat) := by
    rw [← Fin.lt_def]; exact hlt
  have h_rel := h_idx (i_val : Nat) (j_val : Nat) hlt_val hi_lt hj_lt
  rw [getD_eq_get_of_lt xs (i_val : Nat) d hi_lt, getD_eq_get_of_lt xs (j_val : Nat) d hj_lt] at h_rel
  exact h_rel

/-- `List.Pairwise (· ≤ ·)` implies `getD` values are ordered by index for `LinearOrder` types.
For any valid indices `i < j`, `(xs[i]?).getD default ≤ (xs[j]?).getD default`. -/
lemma getD_le_of_pairwise_le {α : Type} [LinearOrder α] [Inhabited α] {xs : List α}
    (h : List.Pairwise (· ≤ ·) xs) (i j : Nat) (h_lt : i < j) (hi : i < xs.length) (hj : j < xs.length) :
    (xs[i]?).getD default ≤ (xs[j]?).getD default := by
  rw [getD_eq_get_of_lt xs i _ hi, getD_eq_get_of_lt xs j _ hj]
  rw [List.pairwise_iff_get] at h
  have h_ij : (⟨i, hi⟩ : Fin xs.length) < (⟨j, hj⟩ : Fin xs.length) := by
    rw [Fin.lt_def]; exact h_lt
  exact h (⟨i, hi⟩ : Fin xs.length) (⟨j, hj⟩ : Fin xs.length) h_ij

/-- If a list is `Pairwise` ordered by `decide (a ≤ b) = true`, then consecutive
adjacent elements are non-decreasing: for any `i` such that `i + 1 < l.length`,
we have `l.get ⟨i, ...⟩ ≤ l.get ⟨i+1, h⟩`. Works for any `LinearOrder` type.

This extracts the adjacent-index property from the full `Pairwise` condition,
which is often needed when relating sorted lists to `Array` indexing. -/
lemma get_le_get_succ_of_pairwise_decide {α : Type} [LinearOrder α] {l : List α}
    (h : List.Pairwise (fun a b => decide (a ≤ b) = true) l) {i : Nat} (hi : i + 1 < l.length) :
    l.get ⟨i, by omega⟩ ≤ l.get ⟨i+1, hi⟩ := by
  revert i
  induction h with
  | nil =>
    intro i hi; simp at hi
  | @cons a l' h_forall h_pairwise ih =>
    intro i hi
    simp at hi
    cases i with
    | zero =>
      simp
      have hpos : 0 < l'.length := by omega
      have hmem : l'.get ⟨0, hpos⟩ ∈ l' := List.get_mem l' ⟨0, hpos⟩
      have hdec : decide (a ≤ l'.get ⟨0, hpos⟩) = true := h_forall _ hmem
      simpa using hdec
    | succ i' =>
      have hi' : i' + 1 < l'.length := by omega
      have h_res := ih hi'
      simpa using h_res

end List

namespace List

/-! ### `zipWith` index properties -/

/-- When two lists have equal length, an index valid for the first is also valid for the second. -/
lemma lt_of_length_eq {l₁ l₂ : List α} (h : l₁.length = l₂.length) {i : Nat}
    (hi : i < l₁.length) : i < l₂.length := by
  omega

/-- If the two input lists have equal length, then the `zipWith`-ed list has the same length. -/
lemma length_zipWith_eq_of_length_eq (f : α → β → γ) {a : List α} {b : List β} (h : a.length = b.length) :
    (zipWith f a b).length = a.length := by
  rw [length_zipWith, h, Nat.min_self]

/-- If an index is within bounds of `zipWith f a b`, then it is within bounds of `a`. -/
lemma lt_of_lt_zipWith_length_left {f : α → β → γ} {a : List α} {b : List β} {i : Nat}
    (h : i < (zipWith f a b).length) : i < a.length := by
  rw [length_zipWith] at h
  exact lt_of_lt_of_le h (Nat.min_le_left _ _)

/-- If an index is within bounds of `zipWith f a b`, then it is within bounds of `b`. -/
lemma lt_of_lt_zipWith_length_right {f : α → β → γ} {a : List α} {b : List β} {i : Nat}
    (h : i < (zipWith f a b).length) : i < b.length := by
  rw [length_zipWith] at h
  exact lt_of_lt_of_le h (Nat.min_le_right _ _)

/-- When the index is within bounds, `getD` on a `zipWith`-ed list distributes over `f`:
`(zipWith f a b).getD i default = f (a.getD i default) (b.getD i default)`. -/
lemma getD_zipWith_eq (f : α → β → γ) (a : List α) (b : List β) (i : Nat)
    [Inhabited α] [Inhabited β] [Inhabited γ]
    (hi : i < (zipWith f a b).length) :
    (zipWith f a b).getD i default = f (a.getD i default) (b.getD i default) := by
  have ha := lt_of_lt_zipWith_length_left hi
  have hb := lt_of_lt_zipWith_length_right hi
  have ha_eq : a.getD i default = a[i] := by
    simpa using getD_eq_getElem a default ha
  have hb_eq : b.getD i default = b[i] := by
    simpa using getD_eq_getElem b default hb
  calc
    (zipWith f a b).getD i default = (zipWith f a b)[i] := by
      simpa using getD_eq_getElem (zipWith f a b) default hi
    _ = f (a[i]) (b[i]) := by rw [getElem_zipWith (h := hi)]
    _ = f (a.getD i default) (b.getD i default) := by rw [ha_eq, hb_eq]

/-! ### `zipWithIndex` — zip two lists with an index-dependent function -/

/-- `zipWithIndex f k a b` zips lists `a` and `b` using a function `f` that depends on
the current index, starting at `k` and incrementing by 1 for each element.
If the lists have different lengths, the result is truncated to the shorter length.

Example: `zipWithIndex (λ i a b => (i, a, b)) 0 [x, y] [u, v] = [(0, x, u), (1, y, v)]`. -/
def zipWithIndex (f : Nat → α → β → γ) (k : Nat) : List α → List β → List γ
  | [], [] => []
  | a :: as, b :: bs => f k a b :: zipWithIndex f (k + 1) as bs
  | _, _ => []

/-- The length of `zipWithIndex` equals the length of the first input list,
provided the two input lists have equal length. -/
lemma zipWithIndex_length (f : Nat → α → β → γ) (k : Nat) (la : List α) (lb : List β) (h : la.length = lb.length) :
    (zipWithIndex f k la lb).length = la.length := by
  induction la generalizing lb k with
  | nil =>
    have hnil : lb = [] := by
      have h0 : lb.length = 0 := by simpa using h.symm
      exact List.length_eq_zero_iff.mp h0
    simp [zipWithIndex, hnil]
  | cons a as ih =>
    cases lb with
    | nil => simp at h
    | cons b bs =>
      simp [zipWithIndex]
      have hlen : as.length = bs.length := by
        simp at h; exact h
      exact ih (k + 1) bs hlen

/-- Accessing the `i`-th element of `zipWithIndex f k la lb` (when both lists have equal length
and `i` is in bounds) gives `f (k + i) la[i]! lb[i]!`. -/
lemma zipWithIndex_getElem! [Inhabited α] [Inhabited β] [Inhabited γ] (f : Nat → α → β → γ) (k i : Nat)
    (la : List α) (lb : List β) (h : la.length = lb.length) (hi : i < la.length) :
    (zipWithIndex f k la lb)[i]! = f (k + i) la[i]! lb[i]! := by
  have hreslen : i < (zipWithIndex f k la lb).length := by
    rw [zipWithIndex_length f k la lb h]
    exact hi
  have hblen : i < lb.length := by
    rw [← h]
    exact hi
  rw [getElem!_pos (zipWithIndex f k la lb) i hreslen,
      getElem!_pos la i hi,
      getElem!_pos lb i hblen]
  induction la generalizing lb k i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a as ih =>
    cases lb with
    | nil =>
      simp at h
    | cons b bs =>
      have hlen : as.length = bs.length := by
        simp at h; exact h
      match i with
      | 0 =>
        simp [zipWithIndex]
      | i' + 1 =>
        simp [zipWithIndex]
        have hi' : i' < as.length := by
          simpa using hi
        have h_ih := ih (k + 1) i' bs hlen hi'
        have hcoeff : (k + 1) + i' = k + (i' + 1) := by omega
        rw [h_ih, hcoeff]

end List

namespace List

/-! ### `getZero` — safe indexing for `List Nat` with default `0` -/

/-- Safe list indexing: return the element at position `i`, or `0` if out of bounds.
This is a convenience wrapper around `(l[i]?).getD 0` (equivalently `l.getD i 0`). -/
def getZero (l : List Nat) (i : Nat) : Nat := (l[i]?).getD 0


lemma getZero_eq_getD (l : List Nat) (i : Nat) : getZero l i = l.getD i 0 := rfl

/-- `getZero` on `List.ofFn` returns the function value at the corresponding index. -/
lemma getZero_ofFn {n : Nat} (f : Fin n → Nat) (i : Nat) (h : i < n) :
    getZero (List.ofFn f) i = f ⟨i, h⟩ := by
  simp [getZero, List.getElem?_ofFn, h]

/-- `getZero` on a `List.replicate` returns the replicated value when the index is within bounds. -/
lemma getZero_replicate (size val d : Nat) (hd : d < size) :
    getZero (List.replicate size val) d = val := by
  unfold getZero
  simp [hd]

/-- `getZero` on `(range n).map f` returns `f d` when `d < n`. -/
lemma getZero_map_range (f : Nat → Nat) (n d : Nat) (hd : d < n) :
    getZero ((List.range n).map f) d = f d := by
  unfold getZero
  simp [hd]

/-! ### `sumAtIndices` — sum of list elements at given indices -/

/-- Sum the elements of `xs` at the indices listed in `idxs`.
Elements at out-of-bounds indices default to `0` (the additive identity),
so they contribute nothing to the sum.

For example, `sumAtIndices [a,b,c,d] [0,2,3] = a + c + d`. -/
@[reducible]
def sumAtIndices [AddCommMonoid α] (xs : List α) (idxs : List Nat) : α :=
  (idxs.map (fun i => xs.getD i 0)).foldl (fun acc x => acc + x) 0

/-! ### Indexing from a starting offset -/

/-- Zip a list with indices, starting from `start` (inclusive) and incrementing.
`indexFrom start [a, b, c] = [(start, a), (start+1, b), (start+2, c)]`.
This generalizes `List.enum` which always starts from `0`. -/
def indexFrom (start : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (start, x) :: indexFrom (start+1) xs

/-- `indexFrom` preserves the length of the original list. -/

theorem indexFrom_length (start : Nat) (xs : List α) : (indexFrom start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [indexFrom, ih]

end List

namespace List

/-! ### `headD` membership lemmas -/

/-- If a list is nonempty, its `headD` with any default is in the list. -/
lemma headD_mem_of_ne_nil {α : Type} (d : α) (l : List α) (h : l ≠ []) : l.headD d ∈ l := by
  cases l
  · contradiction
  · simp

/-- If a list has positive length, its `headD` with any default is in the list. -/
lemma headD_mem_of_pos_length {α : Type} (d : α) (l : List α) (hpos : 0 < l.length) :
    l.headD d ∈ l :=
  headD_mem_of_ne_nil d l (by
    intro h
    rw [h, List.length_nil] at hpos
    exact Nat.lt_irrefl 0 hpos)

/-- If `a ∈ l` and `x` is in a `replicate` of `a`, then `x ∈ l`.
This lemma chains through `List.mem_replicate.mp` to show that any element
of a replicated list belongs to any list containing the replicated value.

Useful when reasoning about `List.replicate` results in membership chains,
e.g., when a chosen value is replicated and each copy must be shown to
belong to some original container. -/
lemma mem_of_mem_replicate {α : Type} {a : α} {l : List α} (ha : a ∈ l) (n : Nat) {x : α}
    (hx : x ∈ List.replicate n a) : x ∈ l := by
  rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
  exact ha

/-! ### `headD` map lemmas -/

/-- `headD` of a map over a non-empty list uses the head element as the function argument. -/
lemma headD_map_cons {α β : Type} (f : α → β) (x : α) (xs : List α) (d : β) :
    ((x :: xs).map f).headD d = f x := by
  simp

/-! ### `getLast?` — last element of a list -/

/-- `List.getLast?` of a non-empty list is never `none`. -/
lemma getLast?_ne_none_of_ne_nil {α : Type u} {l : List α} (h : l ≠ []) :
    l.getLast? ≠ none := by
  rcases List.exists_cons_of_ne_nil h with ⟨a, t, rfl⟩
  induction t generalizing a with
  | nil => simp
  | cons b t ih => simp [ih b]

/-- For a nonempty list, `Option.getD (xs.getLast?) d` extracts the last element,
ignoring the default `d`. This generalizes the interaction between `Option.getD`
and `List.getLast?`, making it reusable for any type `α`. -/
lemma option_getD_getLast?_eq_getLast {α : Type u} {xs : List α} {d : α} (hne : xs ≠ []) :
    Option.getD (xs.getLast?) d = xs.getLast hne := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      simp [ih hne']

end List

namespace List

/-! ### 1-indexed element access -/

/-- Access the n-th element of a list (1-indexed), returning `default` if `n = 0` or out of bounds. -/
def getOneBased (l : List α) (default : α) (n : Nat) : α :=
  match n with
  | 0 => default
  | n'+1 => (l[n']?).getD default

end List

namespace List

/-! ### Even/odd position extraction -/

/-- Extract elements at even positions (0-indexed) from a list.
For example, `evenPositions ['a','b','c','d'] = ['a','c']`. -/
def evenPositions {α : Type} (l : List α) : List α :=
  (l.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)

/-- Extract elements at odd positions (0-indexed) from a list.
For example, `oddPositions ['a','b','c','d'] = ['b','d']`. -/
def oddPositions {α : Type} (l : List α) : List α :=
  (l.zipIdx.filter (fun p => p.2 % 2 = 1)).map (fun p => p.1)

end List

namespace List

/-! ### `getElem?` and `getElem!` bridge (continued) -/

/-- When `i` is in bounds, `l[i]! = l[i]`.  This connects the total `getElem!` (which uses
`Inhabited.default` for out‑of‑bounds) to the pure `getElem` (which needs a proof). -/
lemma get!_eq_getElem_of_lt {α : Type u} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) :
    l[i]! = l[i] := by
  simp [h]

/-- `l[i]!` is a member of `l` when `i < l.length`. -/
lemma get!_mem (l : List α) [Inhabited α] (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  induction l generalizing i with
  | nil =>
    simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ i' =>
      have heq : (x :: xs)[i'+1]! = xs[i']! := by simp
      rw [heq]
      have hi' : i' < xs.length := by
        simpa [List.length_cons] using h
      apply List.mem_cons_of_mem
      exact ih i' hi'

/-- When `i` is in bounds, the optional lookup `l[i]?` is not `none`. -/
lemma getElem?_isSome_of_lt {l : List α} {i : ℕ} (h : i < l.length) : l[i]?.isSome := by
  rw [List.getElem?_eq_getElem h]
  simp

end List


namespace List


/-! ### Finding the index of an element matching a predicate, starting from an offset -/

/-- Find the first index `k ≥ offset` such that `p lst[k - offset]` is true.
Returns `none` if no element in `lst` satisfies `p`.
This is the `Bool`-predicate version: for the equality-check version see `findIdxFrom`.
See also `List.findIdx?` in Std for searching from offset 0. -/
def findIdxBy {α : Type} (lst : List α) (p : α → Bool) (offset : Nat) : Option Nat :=
  match lst with
  | []        => none
  | x :: xs =>
    if p x then
      some offset
    else
      findIdxBy xs p (offset + 1)

/-- If `findIdxBy` finds an index `i`, then `i` is within the bounds of the list
(shifted by `offset`): `i < offset + lst.length`. -/
lemma findIdxBy_bound {α : Type} (lst : List α) (offset i : Nat) (p : α → Bool)
    (h : findIdxBy lst p offset = some i) : i < offset + lst.length := by
  induction' lst with x rest ih generalizing offset
  · simp [findIdxBy] at h
  · simp [findIdxBy] at h
    split at h
    · injection h with h_eq; subst h_eq
      have hpos : 0 < (x :: rest).length := by simp
      calc
        offset = offset + 0 := by simp
        _ < offset + (x :: rest).length := Nat.add_lt_add_left hpos offset
    · have h_ih := ih (offset + 1) h
      simpa [add_comm, add_left_comm, add_assoc] using h_ih

/-! ### Finding the first / last index satisfying a Bool predicate -/

/-- If there exists an index where `getElem!` satisfies `p`, then `findIdx?` is not `none`.
This bridges the `getElem!`-based existence hypothesis (common in finite verification)
to the `Option`-based `findIdx?` API. -/
lemma findIdx?_ne_none_of_exists_getElem {α : Type _} [Inhabited α] (l : List α) (p : α → Bool)
    (h : ∃ i, i < l.length ∧ p (l[i]!) = true) : l.findIdx? p ≠ none := by
  rcases h with ⟨i, hi, hp⟩
  intro heq
  have hall := (List.findIdx?_eq_none_iff.mp heq)
  have mem : l[i]! ∈ l := getElem!_mem_of_lt hi
  have hfalse := hall (l[i]!) mem
  rw [hp] at hfalse
  simp at hfalse

/-- If `y` is a member of `tl`, then `List.findIdx?` with equality comparison finds some index.
This bridges `List.mem` to `List.findIdx?` for the specific case of equality predicates. -/
lemma findIdx?_some_of_mem [DecidableEq α] (y : α) (tl : List α) (h_mem : y ∈ tl) :
    ∃ n, List.findIdx? (fun z => z = y) tl = some n := by
  induction' tl with hd tl' ih
  · simp at h_mem
  · rw [List.findIdx?_cons]
    have h_cases : y = hd ∨ y ∈ tl' := by simpa using h_mem
    rcases h_cases with (rfl | h_mem')
    · simp
    · by_cases h_eq : y = hd
      · subst h_eq; simp
      · have hne_bool : ((hd = y) : Bool) = false := by simp [Ne.symm h_eq]
        split
        · simp [hne_bool]
        · simp
          rcases ih h_mem' with ⟨n, hn⟩
          exact ⟨n + 1, by simp [hn]⟩

/-- Find the first index where element satisfies `p` in list `l`. Returns `0` if none found.
This is a `Nat`-returning wrapper around `List.findIdx?` (which returns `Option Nat`).
See also `findIdxBy` for an offset parameter and `findIdxFrom` for equality search. -/
def findFirstIdx {α : Type _} (p : α → Bool) (l : List α) : Nat :=
  match l.findIdx? p with
  | some i => i
  | none   => 0

/-- Find the last index where element satisfies `p` in list `l`. Returns `0` if none found.
Searches by reversing the list and calling `findIdx?` on the reversed list,
then converting the index back to the original order. -/
def findLastIdx {α : Type _} (p : α → Bool) (l : List α) : Nat :=
  match l.reverse.findIdx? p with
  | some k => l.length - 1 - k
  | none   => 0

/-- `findFirstIdx p l` is in bounds if any element satisfies `p`. -/
lemma findFirstIdx_lt_length_of_exists {α : Type _} [Inhabited α] (l : List α) (p : α → Bool)
    (h : ∃ i, i < l.length ∧ p (l[i]!) = true) : findFirstIdx p l < l.length := by
  have hne := findIdx?_ne_none_of_exists_getElem l p h
  unfold findFirstIdx
  cases hres : l.findIdx? p with
  | none => exact (hne hres).elim
  | some i =>
    rcases (List.findIdx?_eq_some_iff_getElem.mp hres) with ⟨hi, _, _⟩
    exact hi

/-- The element at `findFirstIdx p l` satisfies `p` if any element does. -/
lemma findFirstIdx_satisfies_of_exists {α : Type _} [Inhabited α] (l : List α) (p : α → Bool)
    (h : ∃ i, i < l.length ∧ p (l[i]!) = true) : p (l[findFirstIdx p l]!) = true := by
  have hne := findIdx?_ne_none_of_exists_getElem l p h
  unfold findFirstIdx
  cases hres : l.findIdx? p with
  | none => exact (hne hres).elim
  | some i =>
    rcases (List.findIdx?_eq_some_iff_getElem.mp hres) with ⟨hi, hp', _⟩
    rw [getElem!_eq_getElem_of_lt hi]
    exact hp'

/-- If `l.findIdx? p = some i`, then `i < l.length`. -/
lemma findIdx?_some_lt_length {α : Type} {l : List α} {p : α → Bool} {i : Nat}
    (h : l.findIdx? p = some i) : i < l.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left

/-- Relates `findIdx?.getD 0` to `findIdx` when the predicate holds for some element. -/
lemma getD_findIdx?_eq_findIdx_of_exists {α : Type} {l : List α} {p : α → Bool}
    (h : ∃ x ∈ l, p x = true) : (l.findIdx? p).getD 0 = l.findIdx p := by
  simp [List.findIdx?_eq_some_of_exists h]

/-- If some element satisfies the predicate, `findIdx?.getD 0` is less than the list length. -/
lemma findIdx?_getD_lt_length_of_exists {α : Type} {l : List α} {p : α → Bool}
    (h : ∃ x ∈ l, p x = true) : (l.findIdx? p).getD 0 < l.length := by
  rw [getD_findIdx?_eq_findIdx_of_exists h]
  exact List.findIdx_lt_length_of_exists h

/-- `findIdx` for an equality predicate is the first occurrence: if `l[i] = x`, then
`l.findIdx (fun a => decide (a = x)) ≤ i`. -/
lemma findIdx_eq_le_of_getElem_eq {α : Type} [DecidableEq α] {l : List α} {x : α} {i : Nat}
    (hi : i < l.length) (hx : l[i] = x) : l.findIdx (fun a => decide (a = x)) ≤ i := by
  by_contra! h_gt
  have hi_lt_findIdx : i < l.findIdx (fun a => decide (a = x)) := h_gt
  have h_not_p_i : (fun a => decide (a = x)) l[i] = false := List.not_of_lt_findIdx hi_lt_findIdx
  simp [hx] at h_not_p_i

/-! ### Finding the first pair of indices satisfying a predicate -/

/-- Find the first pair of indices `(i, j)` with `i < j` such that `p xs[i] xs[j]` holds,
using logical index `startIdx` as the base. Returns `none` if no such pair exists. -/
def findFirstPair {α : Type} (xs : List α) (startIdx : Nat) (p : α → α → Bool) : Option (Nat × Nat) :=
  match xs with
  | [] => none
  | x :: rest =>
    match findIdxBy rest (p x) (startIdx + 1) with
    | some j => some (startIdx, j)
    | none => findFirstPair rest (startIdx + 1) p

/-- Properties of a pair found by `findFirstPair`: `startIdx ≤ i`, `i < j`,
and both indices are bounded by `startIdx + xs.length`. -/
lemma findFirstPair_properties {α : Type} (xs : List α) (startIdx i j : Nat) (p : α → α → Bool)
    (h : findFirstPair xs startIdx p = some (i, j)) :
    startIdx ≤ i ∧ i < j ∧ i < startIdx + xs.length ∧ j < startIdx + xs.length := by
  induction' xs with x rest ih generalizing startIdx i j
  · simp [findFirstPair] at h
  · rw [findFirstPair] at h
    cases hdj : findIdxBy rest (p x) (startIdx + 1) with
    | none =>
      simp [hdj] at h
      have h_ih := ih (startIdx + 1) i j h
      rcases h_ih with ⟨hge, hlt, hbnd_i, hbnd_j⟩
      refine ⟨?_, hlt, ?_, ?_⟩
      · omega
      · simpa [add_comm, add_left_comm, add_assoc] using hbnd_i
      · simpa [add_comm, add_left_comm, add_assoc] using hbnd_j
    | some k =>
      simp [hdj] at h
      rcases h with ⟨hi_eq, hj_eq⟩
      subst hi_eq; subst hj_eq
      have h_bound := findIdxBy_bound rest (startIdx + 1) k (p x) hdj
      have h_ge : startIdx + 1 ≤ k := by
        have h_ge_inner : ∀ (lst : List α) (off k' : Nat) (pred : α → Bool),
            findIdxBy lst pred off = some k' → off ≤ k' := by
          intro lst off k' pred hff
          induction' lst with r rs ih_inner generalizing off
          · simp [findIdxBy] at hff
          · simp [findIdxBy] at hff
            split at hff
            · injection hff with h_eq; subst h_eq; exact Nat.le_refl off
            · have h_ih := ih_inner (off + 1) hff
              omega
        exact h_ge_inner rest (startIdx + 1) k (p x) hdj
      have h_lt : startIdx < k := by omega
      refine ⟨Nat.le_refl startIdx, h_lt, ?_, ?_⟩
      · have hpos : 0 < (x :: rest).length := by simp
        calc
          startIdx = startIdx + 0 := by simp
          _ < startIdx + (x :: rest).length := Nat.add_lt_add_left hpos startIdx
      · simpa [add_comm, add_left_comm, add_assoc] using h_bound

/-- Find the first pair of indices `(i, j)` such that `p i j xs[i] xs[j]` holds,
scanning in row-major order (i from 0 upward, then j from 0 upward for each i).
Returns `none` if no such pair exists.

The predicate receives both indices and the values at those positions,
unlike `findFirstPair` which passes only values and requires `i < j`. -/
def findFirstIndexedPair {α : Type} (xs : List α) (p : Nat → Nat → α → α → Bool) : Option (Nat × Nat) :=
  let n := xs.length
  (List.range n).findSome? (fun i =>
    (List.range n).findSome? (fun j =>
      match xs[i]?, xs[j]? with
      | some a, some b => if p i j a b then some (i, j) else none
      | _, _ => none))

/-! ### Finding the index of a specific element starting from an offset -/

/-- Find the first index `k ≥ i` such that `lst[k - i] = c`.
Returns `none` if `c` is not found in the list. -/
def findIdxFrom {α : Type u} [DecidableEq α] (lst : List α) (c : α) (i : Nat) : Option Nat :=
  match lst with
  | []      => none
  | x::xs   => if x = c then some i else findIdxFrom xs c (i + 1)

/-- If `x ≠ c`, searching for `c` in `x :: xs` from offset `i` is the same as
searching in `xs` from offset `i + 1`. -/
lemma findIdxFrom_cons_ne {α : Type u} [DecidableEq α] {x c : α} (h : x ≠ c) (xs : List α) (i : Nat) :
    findIdxFrom (x :: xs) c i = findIdxFrom xs c (i + 1) := by
  simp [findIdxFrom, h]

/-- `findIdxFrom` returns `some` (found) iff the target element is in the list.
The starting offset `i` does not affect membership — the search covers the entire list. -/
lemma findIdxFrom_isSome_iff_mem {α : Type u} [DecidableEq α] (xs : List α) (a : α) (i : Nat) :
    (findIdxFrom xs a i).isSome ↔ a ∈ xs := by
  induction' xs with x xs ih generalizing i
  · simp [findIdxFrom]
  · simp [findIdxFrom]
    constructor
    · intro h
      by_cases hx : x = a
      · subst hx; exact Or.inl rfl
      · simp [hx] at h
        have hmem := (ih (i+1)).mp h
        exact Or.inr hmem
    · intro h
      rcases h with (h | h)
      · subst h; simp
      · by_cases hx : x = a
        · subst hx; simp
        · simp [hx]
          exact (ih (i+1)).mpr h

/-- Specification for `findIdxFrom`: either the element is not found (returns `none`
and no list entry matches), or it is found at position `k` and returns `some (idx + k)`,
where `k < xs.length` and `xs[k]? = some a`. -/
lemma findIdxFrom_spec {α : Type u} [DecidableEq α] (xs : List α) (a : α) (idx : Nat) :
    (findIdxFrom xs a idx = none ∧ ∀ (k : Nat), k < xs.length → xs[k]? ≠ some a)
    ∨ (∃ (k : Nat), k < xs.length ∧ xs[k]? = some a ∧
      findIdxFrom xs a idx = some (idx + k)) := by
  induction xs generalizing idx with
  | nil =>
    left
    constructor
    · rfl
    · intro k hk
      simp at hk
  | cons x xs ih =>
    by_cases h : x = a
    · -- h : x = a
      have h_aux : findIdxFrom (x :: xs) a idx = some idx := by
        simp [findIdxFrom, h]
      rw [h_aux]
      right
      refine ⟨0, by simp, ?_, ?_⟩
      · simp [h]
      · rfl
    · -- h : x ≠ a
      have h_aux : findIdxFrom (x :: xs) a idx =
          findIdxFrom xs a (idx + 1) := by
        simp [findIdxFrom, h]
      rw [h_aux]
      have h_ih := ih (idx + 1)
      rcases h_ih with (⟨hneg, hall⟩ | ⟨k, hk, hget, hval⟩)
      · -- not found in xs
        left
        constructor
        · exact hneg
        · intro k hk_len
          match k with
          | 0 =>
            simp [h]
          | k'+1 =>
            have hk'_lt : k' < xs.length :=
              Nat.lt_of_succ_lt_succ (by simpa using hk_len)
            simp
            exact hall k' hk'_lt
      · -- found at position k in xs
        right
        refine ⟨k+1, ?_, ?_, ?_⟩
        · -- k+1 < (x::xs).length
          simpa using Nat.succ_lt_succ hk
        · -- (x::xs)[k+1]? = some a
          simp [hget]
        · -- findIdxFrom xs a (idx+1) = some (idx + (k+1))
          rw [hval]
          simp [add_assoc, add_comm, add_left_comm]

/-! ### First index of an element (fallback to length) -/

/-- Find the first index of `a` in `l` via direct recursion.
Returns `l.length` if `a` is not in `l`. This is useful for comparisons:
a missing element has the largest possible "index" (the list length). -/
def firstIdx {α : Type} [DecidableEq α] (l : List α) (a : α) : Nat :=
  match l.findIdx? (· = a) with
  | some i => i
  | none => l.length


lemma firstIdx_nil {α : Type} [DecidableEq α] (a : α) : firstIdx [] a = 0 := rfl

/-- `firstIdx` for `x :: xs` when `x = a` returns `0`. -/

lemma firstIdx_cons_eq {α : Type} [DecidableEq α] (x : α) (xs : List α) (a : α) (h : x = a) :
    firstIdx (x :: xs) a = 0 := by
  subst h; unfold firstIdx; simp

/-- `firstIdx` for `x :: xs` when `x ≠ a` is `firstIdx xs a + 1`. -/
lemma firstIdx_cons_ne {α : Type} [DecidableEq α] {x : α} {xs : List α} {a : α} (h : x ≠ a) :
    firstIdx (x :: xs) a = firstIdx xs a + 1 := by
  unfold firstIdx
  have hfind : (x :: xs).findIdx? (· = a) = (xs.findIdx? (· = a)).map (· + 1) := by
    simp [h]
  rw [hfind]
  cases hxs : xs.findIdx? (· = a) with
  | none =>
    simp [hxs, firstIdx, length_cons]
  | some i =>
    simp [hxs, firstIdx]

/-- If `a` is in `l`, then `firstIdx l a < l.length`. -/
lemma firstIdx_lt_length_of_mem {α : Type} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    firstIdx l a < l.length := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = a
    · simp [firstIdx_cons_eq x xs a hx]
    · rw [firstIdx_cons_ne hx]
      have ha : a ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      simpa using Nat.succ_lt_succ (ih ha)

/-- If `firstIdx l a = l.length`, then `a` is not in `l`. -/
lemma not_mem_of_firstIdx_eq_length {α : Type} [DecidableEq α] {l : List α} {a : α}
    (h : firstIdx l a = l.length) : a ∉ l := by
  intro hmem
  have hlt : firstIdx l a < l.length := firstIdx_lt_length_of_mem hmem
  omega

/-- `a ∈ l` iff `firstIdx l a < l.length`. -/
lemma firstIdx_lt_length_iff_mem {α : Type} [DecidableEq α] {l : List α} {a : α} :
    firstIdx l a < l.length ↔ a ∈ l := by
  constructor
  · intro hlt
    induction' l with x xs ih generalizing a
    · simp [firstIdx] at hlt
    · by_cases hx : x = a
      · subst hx; simp
      · rw [firstIdx_cons_ne hx, length_cons] at hlt
        have hne : firstIdx xs a < xs.length := by omega
        have hmem := ih hne
        simp [hx, hmem]
  · exact firstIdx_lt_length_of_mem

/-- `firstIdx l a ≤ l.length` for any `l` and `a`.
This holds trivially: either `a ∈ l` and `firstIdx l a < l.length`
(by `firstIdx_lt_length_of_mem`), or `a ∉ l` and `firstIdx l a = l.length`. -/
lemma firstIdx_le_length {α : Type} [DecidableEq α] (l : List α) (a : α) :
    firstIdx l a ≤ l.length := by
  unfold firstIdx
  split
  · next i h =>
    have hi := (List.findIdx?_eq_some_iff_getElem.mp h).1
    exact Nat.le_of_lt hi
  · exact Nat.le_refl _

/-! ### Checking a position-dependent predicate on all elements -/

/-- Checks that a position-dependent predicate holds for all elements in a list,
where the predicate receives the (zero-based) position offset by `start`. -/
def allIdx {α : Type} (p : Nat → α → Bool) (xs : List α) (start : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => p start x && allIdx p xs' (start + 1)

/-- Specification lemma for `allIdx`: the predicate holds for all elements exactly when
`p (start + i) xs[i]` is true for every index `i` within bounds. -/
lemma allIdx_spec {α : Type} [Inhabited α] (p : Nat → α → Bool) (xs : List α) (start : Nat) :
    allIdx p xs start = true ↔
    ∀ i, i < xs.length → p (start + i) ((xs[i]?).getD default) := by
  induction' xs with x xs ih generalizing start
  · simp [allIdx]
  · simp [allIdx, List.length_cons]
    constructor
    · rintro ⟨hx, hxs⟩ i hi
      match i with
      | 0 => simp [hx]
      | j+1 =>
        have hj_len : j < xs.length := by omega
        have h_ih := (ih (start + 1)).mp hxs j hj_len
        simpa [add_comm, add_left_comm, add_assoc] using h_ih
    · intro h_all
      have h0 : 0 < (x :: xs).length := by simp
      have h_all0 := h_all 0 h0
      simp at h_all0
      have hx : p start x := h_all0
      have hxs : allIdx p xs (start + 1) = true := by
        apply (ih (start + 1)).mpr
        intro j hj
        have hjs : j + 1 < (x :: xs).length := by
          simpa [List.length_cons] using Nat.succ_lt_succ hj
        have h_js := h_all (j + 1) hjs
        simpa [add_comm, add_left_comm, add_assoc] using h_js
      exact And.intro hx hxs

/-! ### Index of element in list -/

/-- Find the index of the first occurrence of `i` in `l`.
Returns `0` if `i` is not found in the list. -/
def idx {α : Type} [DecidableEq α] (l : List α) (i : α) : Nat :=
  match l with
  | [] => 0
  | x :: xs => if x = i then 0 else Nat.succ (idx xs i)


theorem idx_nil {α : Type} [DecidableEq α] (i : α) : idx [] i = 0 :=
  rfl


theorem idx_cons_self {α : Type} [DecidableEq α] (x : α) (xs : List α) : idx (x :: xs) x = 0 := by
  unfold idx; simp

theorem idx_cons_ne {α : Type} [DecidableEq α] (x i : α) (xs : List α) (h : x ≠ i) :
    idx (x :: xs) i = Nat.succ (idx xs i) := by
  simp [idx, h]

/-! ### Finding the first element where a numeric function equals a target -/

/-- Find the first element `a` in `l` where `f a = target`. Returns `default` if not found.
Uses `[Inhabited α]` to provide a default value, analogous to `Option.getD default`. -/
def findFirstBy {α : Type _} (f : α → Nat) (l : List α) (target : Nat) [Inhabited α] : α :=
  match l with
  | [] => default
  | h :: t => if f h = target then h else findFirstBy f t target

/-- If there exists an element `s` in `l` with `f s = target`, then `findFirstBy` returns an element
satisfying `f result = target`. -/
lemma f_findFirstBy {α : Type _} [DecidableEq α] [Inhabited α] (f : α → Nat) (l : List α) (target : Nat) (s : α)
    (hs : s ∈ l) (hfs : f s = target) : f (findFirstBy f l target) = target := by
  induction' l with hd tl ih
  · simp at hs
  · have hs_cases : s = hd ∨ s ∈ tl := by simpa using hs
    unfold findFirstBy
    split
    · next h_eq => exact h_eq
    · next h_ne =>
      rcases hs_cases with (rfl | hs_tl)
      · exfalso; exact h_ne hfs
      · exact ih hs_tl

/-- If there exists an element `s` in `l` with `f s = target`, then `findFirstBy` returns an element
that belongs to `l`. -/
lemma mem_findFirstBy {α : Type _} [DecidableEq α] [Inhabited α] (f : α → Nat) (l : List α) (target : Nat) (s : α)
    (hs : s ∈ l) (hfs : f s = target) : findFirstBy f l target ∈ l := by
  induction' l with hd tl ih
  · simp at hs
  · have hs_cases : s = hd ∨ s ∈ tl := by simpa using hs
    unfold findFirstBy
    split
    · next h_eq => simp
    · next h_ne =>
      rcases hs_cases with (rfl | hs_tl)
      · exfalso; exact h_ne hfs
      · apply List.mem_cons_of_mem; exact ih hs_tl

/-- `findFirstBy` returns an element whose index (via `List.idx`) in the list is minimal among all
elements `x` with `f x = target`. -/
lemma findFirstBy_idx_minimal {α : Type _} [DecidableEq α] [Inhabited α] (f : α → Nat) (l : List α) (target : Nat)
    (x : α) (hxmem : x ∈ l) (hfx : f x = target) :
    idx l (findFirstBy f l target) ≤ idx l x := by
  induction l generalizing x with
  | nil => simp at hxmem
  | cons hd tl ih =>
    have hx_cases : x = hd ∨ x ∈ tl := by simpa using hxmem
    unfold findFirstBy
    split
    · next h_eq =>
      have h_idx : idx (hd :: tl) hd = 0 := by simp [idx]
      rw [h_idx]
      exact Nat.zero_le _
    · next h_ne =>
      rcases hx_cases with (rfl | hx_tl)
      · rw [hfx] at h_ne
        exact absurd rfl h_ne
      · have hx_ne_hd : x ≠ hd := by
          intro heq; subst heq; rw [hfx] at h_ne; exact h_ne rfl
        have h_result : f (findFirstBy f tl target) = target :=
          f_findFirstBy f tl target x hx_tl hfx
        have h_result_mem_tl : findFirstBy f tl target ∈ tl :=
          mem_findFirstBy f tl target x hx_tl hfx
        have h_result_ne_hd : findFirstBy f tl target ≠ hd := by
          intro heq; subst heq; rw [h_result] at h_ne; exact h_ne rfl
        rw [idx_cons_ne hd (findFirstBy f tl target) tl (Ne.symm h_result_ne_hd)]
        rw [idx_cons_ne hd x tl (Ne.symm hx_ne_hd)]
        have h_ih := ih x hx_tl hfx
        omega

/-- Specification for `findFirstBy` with an upper-bound hypothesis:
if `m` is an upper bound of `f` over `l` and `m` is attained (i.e., `m` is the maximum value),
then `findFirstBy f l m` partitions `l` into `l₁ ++ result :: l₂` where:
- All elements in `l₁` have `f a < m` (they are strictly below the maximum)
- `f result = m` (the result attains the maximum)

This is the key lemma for constructing "the first element achieving the maximum"
from precomputed max-value information. -/
lemma findFirstBy_spec {α : Type _} [Inhabited α] (f : α → Nat) (l : List α) (m : Nat)
    (hm_upper : ∀ a ∈ l, f a ≤ m)
    (hm_exists : ∃ a ∈ l, f a = m) :
    ∃ l₁ l₂, l = l₁ ++ (findFirstBy f l m) :: l₂ ∧ (∀ a ∈ l₁, f a < m) ∧ f (findFirstBy f l m) = m := by
  induction' l with x xs ih generalizing m
  · obtain ⟨a, ha, _⟩ := hm_exists
    exact absurd ha (by simp)
  · by_cases hx : f x = m
    · refine ⟨[], xs, ?_, ?_, ?_⟩
      · simp [findFirstBy, hx]
      · simp
      · simp [findFirstBy, hx]
    · have hx_lt_m : f x < m := by
        have hle := hm_upper x (List.Mem.head _)
        exact Nat.lt_of_le_of_ne hle hx
      have hm_exists' : ∃ a' ∈ xs, f a' = m := by
        obtain ⟨a'', ha'', hm_eq⟩ := hm_exists
        cases ha'' with
        | head _ => exact absurd hm_eq hx
        | tail _ ha'' => exact ⟨a'', ha'', hm_eq⟩
      have hm_upper' : ∀ a' ∈ xs, f a' ≤ m := by
        intro a' ha'
        exact hm_upper a' (List.Mem.tail x ha')
      obtain ⟨l₁, l₂, hxs, hall, hlen⟩ := ih m hm_upper' hm_exists'
      have hffm : findFirstBy f (x :: xs) m = findFirstBy f xs m := by
        simp [findFirstBy, hx]
      refine ⟨x :: l₁, l₂, ?_, ?_, ?_⟩
      · rw [hffm]
        exact congrArg (fun t => x :: t) hxs
      · intro a ha
        cases ha with
        | head _ => exact hx_lt_m
        | tail _ ha' => exact hall a ha'
      · rw [hffm]
        exact hlen

/-! ### Finding all positions of an element -/

/--
Find all indices `i` such that `xs[i]? = some x`.
This is a general-purpose helper for locating elements in a list.
-/
def positionsOf {α : Type} [DecidableEq α] (x : α) (xs : List α) : List Nat :=
  (range xs.length).filter (fun i => xs[i]? = some x)

/--
Every index returned by `positionsOf` is within the bounds of the input list.
-/
lemma positionsOf_lt_length {α : Type} [DecidableEq α] {x : α} {xs : List α} {i : Nat}
    (h : i ∈ positionsOf x xs) : i < xs.length := by
  unfold positionsOf at h
  rcases mem_filter.mp h with ⟨hmem, _⟩
  simpa using hmem

/--
`positionsOf` returns a subset of the range of valid indices.
-/
lemma positionsOf_subset_range {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    positionsOf x xs ⊆ range xs.length := by
  intro i hi
  have hlt := positionsOf_lt_length hi
  exact mem_range.mpr hlt


end List

namespace List

/-! # Lemmas about `List.idxOf`

This module provides lemmas about the standard library's `List.idxOf` function,
which returns the first index where a given element occurs in a list (or
`length` if the element is not found).
-/

/-- If `l[i] = a` and `i < l.length`, then `idxOf a l ≤ i`.
This is because `idxOf` returns the first index where `a` occurs. -/
lemma idxOf_le_of_getElem_eq [DecidableEq α] {l : List α} {a : α} {i : Nat}
    (h_lt : i < l.length) (h_eq : l[i] = a) : idxOf a l ≤ i := by
  induction' l with x xs ih generalizing i
  · exact absurd h_lt (Nat.not_lt_zero _)
  · match i with
    | 0 =>
      have hx : x = a := by simpa using h_eq
      simp [hx]
    | i + 1 =>
      have h_lt' : i < xs.length := by
        simpa using h_lt
      have h_eq' : xs[i] = a := by
        simpa using h_eq
      have h_le : idxOf a xs ≤ i := ih h_lt' h_eq'
      by_cases hx : x = a
      · simp [hx]
      · simp [idxOf_cons_ne _ hx, h_le]

/-- If every `a ∈ l` with `a ≤ m` has its first occurrence at or after the first occurrence of `m`,
then for any index `i` before `idxOf m l`, the element `l[i]!` is strictly greater than `m`. -/
lemma getElem_gt_of_lt_idxOf [LinearOrder α] [Inhabited α] [DecidableEq α] {l : List α} {m : α}
    (hfirst : ∀ a ∈ l, a ≤ m → idxOf m l ≤ idxOf a l)
    (i : Nat) (hi : i < idxOf m l) : l[i]! > m := by
  have hi_len : i < l.length := lt_of_lt_of_le hi (idxOf_le_length)
  have hi_val_mem : l[i] ∈ l := getElem_mem hi_len
  by_cases hle : l[i]! ≤ m
  · exfalso
    have hle_val : l[i] ≤ m := by
      have heq : l[i]! = l[i] := by simp [hi_len]
      rw [heq] at hle
      exact hle
    have h_idx_le : idxOf m l ≤ idxOf (l[i]) l := hfirst (l[i]) hi_val_mem hle_val
    have h_idx_i : idxOf (l[i]) l ≤ i :=
      idxOf_le_of_getElem_eq hi_len (by simp [hi_len])
    have h_contra : idxOf m l ≤ i := le_trans h_idx_le h_idx_i
    exact Nat.not_lt_of_le h_contra hi
  · exact lt_of_not_ge hle

end List
