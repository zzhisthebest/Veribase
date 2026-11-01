import Mathlib
import verina.List.Find
import verina.List.Sort

namespace Specific

open List

/-!
# Array utilities

Theorems relating `Array` operations to `List` operations via `toList`,
plus zip-style combinators.
-/

namespace Array

/--
For any array `arr` and index `i` within bounds of `arr.toList`,
the `get!` operation on the array equals the `get!` operation on `arr.toList`.
-/
theorem getElem!_toList {α : Type _} [Inhabited α] (arr : Array α) :
    ∀ i, i < arr.toList.length → arr[i]! = arr.toList[i]! := by
  intro i hi
  have hiArr : i < arr.size := by simpa using hi
  simp [getElem!_def, hiArr, hi, Array.getElem_toList hiArr]

/--
Zip two arrays with a function `f`, producing an array whose length is
`a.size`. The second array `b` is accessed via `getElem!` (requiring
`Inhabited β` for out-of-bounds defaults).
-/
def zipWithLeft {α β γ : Type} [Inhabited β] (f : α → β → γ)
    (a : Array α) (b : Array β) : Array γ :=
  Array.ofFn (fun i : Fin a.size => f a[i] b[i]!)

theorem zipWithLeft_size {α β γ : Type} [Inhabited β] (f : α → β → γ)
    (a : Array α) (b : Array β) :
    (zipWithLeft f a b).size = a.size := by
  simp [zipWithLeft]

theorem zipWithLeft_getElem! {α β γ : Type} [Inhabited α] [Inhabited β]
    [Inhabited γ] (f : α → β → γ) (a : Array α) (b : Array β) (i : Nat)
    (hi : i < a.size) :
    f a[i]! b[i]! = (zipWithLeft f a b)[i]! := by
  rw [getElem!_pos a i hi]
  rw [getElem!_pos (zipWithLeft f a b) i
    (by simpa [zipWithLeft] using hi)]
  simp [zipWithLeft]

/--
Getting the `i`-th element of `zipWithLeft` equals applying `f` to the `i`-th
elements of `a` and `b`. Variant using `i < (zipWithLeft f a b).size` as the
hypothesis and the result-first equality direction.
-/
theorem zipWithLeft_getElem!_result {α β γ : Type} [Inhabited α] [Inhabited β]
    [Inhabited γ] (f : α → β → γ) (a : Array α) (b : Array β) (i : Nat)
    (hi : i < (zipWithLeft f a b).size) :
    (zipWithLeft f a b)[i]! = f a[i]! b[i]! := by
  have hi_a : i < a.size := by simpa [zipWithLeft_size] using hi
  rw [zipWithLeft_getElem! f a b i hi_a]

/--
Zip two arrays element-wise with function `f`.
This is an alias for `Array.zipWith`. The result has length `min a.size b.size`.
-/
@[inline]
def zipWithArray {α β γ : Type u} (f : α → β → γ) (a : Array α) (b : Array β) : Array γ :=
  Array.zipWith f a b

/--
When `a` and `b` have the same size, `zipWithArray` produces an array of that size.
-/
theorem zipWithArray_size_eq_left_of_size_eq {α β γ : Type u}
    (f : α → β → γ) {a : Array α} {b : Array β}
    (h_size : a.size = b.size) :
    (zipWithArray f a b).size = a.size := by
  have h_min : min a.size b.size = a.size := by
    simp [h_size]
  simp [zipWithArray, h_min]

/--
When `a` and `b` have the same size, getting the `i`-th element of `zipWithArray`
equals applying `f` to the `i`-th elements of `a` and `b`.
-/
theorem zipWithArray_getElem!_apply_of_lt {α β γ : Type u}
    [Inhabited α] [Inhabited β] [Inhabited γ]
    (f : α → β → γ) {a : Array α} {b : Array β}
    (h_size : a.size = b.size) {i : Nat} (h_i : i < a.size) :
    f a[i]! b[i]! = (zipWithArray f a b)[i]! := by
  have h_result : i < (zipWithArray f a b).size := by
    simpa [zipWithArray_size_eq_left_of_size_eq f h_size] using h_i
  have h_b : i < b.size := by
    simpa [h_size] using h_i
  rw [getElem!_pos (c := a) (i := i) h_i]
  rw [getElem!_pos (c := b) (i := i) h_b]
  rw [getElem!_pos (c := zipWithArray f a b) (i := i) h_result]
  simp [zipWithArray]

/--
For an index `i` within bounds, `a[i]!` equals the bounded-access `a[i]'hi`.
This is the same as `getElem!_pos` but rewrites to the bounded form.
-/
theorem getElem!_eq_getElem_of_lt {α : Type _} [Inhabited α]
    (a : Array α) (i : Nat) (hi : i < a.size) :
    a[i]! = a[i]'hi := by
  rw [getElem!_pos a i hi]

/--
For an index `i` within bounds, `a[i]` (bounded access) equals `a[i]!` (getElem!).
This is the reverse direction of `getElem!_pos`.
-/
theorem getElem_eq_getElem! {α : Type _} [Inhabited α]
    (a : Array α) (i : Nat) (hi : i < a.size) :
    a[i] = a[i]! := by
  rw [getElem!_pos]

/--
After pushing an element `b`, accessing an existing index `i` (within the original bounds)
with `getElem!` returns the original value. Pushing does not affect earlier elements.
-/
theorem getElem!_push_lt {α : Type _} [Inhabited α]
    (a : Array α) (b : α) (i : Nat) (h : i < a.size) :
    (a.push b)[i]! = a[i]! := by
  have hpush : i < (a.push b).size := by
    rw [Array.size_push]
    omega
  rw [getElem!_pos (a.push b) i hpush, getElem!_pos a i h]
  exact Array.getElem_push_lt a b i h

/--
After setting index `i` to value `v`, accessing index `i` with `getElem!` returns `v`.
-/
theorem getElem!_set_self {α : Type _} [Inhabited α] (a : Array α) (i : Nat) (hi : i < a.size) (v : α) :
    (a.set i v hi)[i]! = v := by
  have hset : i < (a.set i v hi).size := by
    simpa [Array.size_set] using hi
  calc
    (a.set i v hi)[i]! = (a.set i v hi)[i] := getElem!_pos (a.set i v hi) i hset
    _ = v := Array.getElem_set_self a i hi v

/--
After setting index `i` to value `v`, accessing a different index `j` with `getElem!`
returns the original value at `j`.
-/
theorem getElem!_set_ne {α : Type _} [Inhabited α] (a : Array α) (i j : Nat)
    (hi : i < a.size) (hj : j < a.size) (hij : i ≠ j) (v : α) :
    (a.set i v hi)[j]! = a[j]! := by
  have hset : j < (a.set i v hi).size := by
    simpa [Array.size_set] using hj
  calc
    (a.set i v hi)[j]! = (a.set i v hi)[j] := getElem!_pos (a.set i v hi) j hset
    _ = a[j] := Array.getElem_set_ne a i hi v hj hij
    _ = a[j]! := (getElem!_pos a j hj).symm

/--
After setting index `i` to value `v`, accessing `i` returns `v`,
and accessing any other index `k` within bounds returns the original value.
Convenience bundling of `getElem!_set_self` and `getElem!_set_ne`.
-/
theorem getElem!_set_eq_and_ne {α : Type _} [Inhabited α] (a : Array α) (i : Nat) (v : α)
    (hi : i < a.size) :
    (a.set i v hi)[i]! = v ∧ ∀ k, k < a.size → k ≠ i → (a.set i v hi)[k]! = a[k]! := by
  constructor
  · exact getElem!_set_self a i hi v
  · intro k hk hki
    exact getElem!_set_ne a i k hi hk hki.symm v

/--
Set two values in an array in a single pass: `first` at index `i` and `second` at index `j`.
-/
def setTwoValues {α : Type _} (a : Array α) (i j : Nat)
    (first second : α) (hi : i < a.size) (hj : j < a.size) : Array α :=
  (a.set i first hi).set j second (by
    simpa using hj)

theorem size_setTwoValues {α : Type _} (a : Array α) (i j : Nat)
    (first second : α) (hi : i < a.size) (hj : j < a.size) :
    (setTwoValues a i j first second hi hj).size = a.size := by
  unfold setTwoValues
  simp

theorem getElem!_setTwoValues_first {α : Type _} [Inhabited α]
    (a : Array α) (i j : Nat) (first second : α)
    (hi : i < a.size) (hj : j < a.size) (hij : i ≠ j) :
    (setTwoValues a i j first second hi hj)[i]! = first := by
  have hi' : i < (setTwoValues a i j first second hi hj).size := by
    rw [size_setTwoValues]
    exact hi
  rw [getElem!_pos (setTwoValues a i j first second hi hj) i hi']
  unfold setTwoValues
  rw [Array.getElem_set_ne, Array.getElem_set_self]
  exact hij.symm

theorem getElem!_setTwoValues_second {α : Type _} [Inhabited α]
    (a : Array α) (i j : Nat) (first second : α)
    (hi : i < a.size) (hj : j < a.size) :
    (setTwoValues a i j first second hi hj)[j]! = second := by
  have hj' : j < (setTwoValues a i j first second hi hj).size := by
    rw [size_setTwoValues]
    exact hj
  rw [getElem!_pos (setTwoValues a i j first second hi hj) j hj']
  unfold setTwoValues
  rw [Array.getElem_set_self]

theorem getElem!_setTwoValues_of_ne {α : Type _} [Inhabited α]
    (a : Array α) (i j k : Nat) (first second : α)
    (hi : i < a.size) (hj : j < a.size) (hk : k < a.size)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (setTwoValues a i j first second hi hj)[k]! = a[k]! := by
  have hk' : k < (setTwoValues a i j first second hi hj).size := by
    rw [size_setTwoValues]
    exact hk
  rw [getElem!_pos (setTwoValues a i j first second hi hj) k hk',
    getElem!_pos a k hk]
  unfold setTwoValues
  rw [Array.getElem_set_ne, Array.getElem_set_ne]
  · exact hki.symm
  · exact hkj.symm

/--
Set `val` at position `(outerIndex, innerIndex)` in an array of arrays.
`hOuter` guarantees the outer index is in bounds, and `hInner` guarantees
the inner index is in bounds of the selected sub-array.
-/
def setNested {α : Type u} (arr : Array (Array α)) (outerIndex innerIndex : Nat)
    (val : α) (hOuter : outerIndex < arr.size)
    (hInner : innerIndex < (arr[outerIndex]!).size) : Array (Array α) :=
  arr.set outerIndex ((arr[outerIndex]!).set innerIndex val hInner) hOuter

/--
After setting a nested element at `(outerIndex, innerIndex)`, accessing a
*different* outer index `i` returns the original outer sub-array unchanged.
-/
theorem getElem!_setNested_outer_ne {α : Type u}
    (arr : Array (Array α)) (outerIndex innerIndex : Nat) (val : α)
    (hOuter : outerIndex < arr.size) (hInner : innerIndex < (arr[outerIndex]!).size)
    (i : Nat) (hi : i < arr.size) (hne : i ≠ outerIndex) :
    (setNested arr outerIndex innerIndex val hOuter hInner)[i]! = arr[i]! := by
  unfold setNested
  exact getElem!_set_ne arr outerIndex i hOuter hi hne.symm
    ((arr[outerIndex]!).set innerIndex val hInner)

/--
After setting a nested element at `(outerIndex, innerIndex)`, accessing the same
outer index but a *different* inner index `j` returns the original inner value.
-/
theorem getElem!_setNested_inner_ne {α : Type u} [Inhabited α]
    (arr : Array (Array α)) (outerIndex innerIndex : Nat) (val : α)
    (hOuter : outerIndex < arr.size) (hInner : innerIndex < (arr[outerIndex]!).size)
    (j : Nat) (hj : j < (arr[outerIndex]!).size) (hne : j ≠ innerIndex) :
    ((setNested arr outerIndex innerIndex val hOuter hInner)[outerIndex]!)[j]! =
      (arr[outerIndex]!)[j]! := by
  unfold setNested
  rw [getElem!_set_self arr outerIndex hOuter
    ((arr[outerIndex]!).set innerIndex val hInner)]
  exact getElem!_set_ne (arr[outerIndex]!) innerIndex j hInner hj hne.symm val

/--
After setting a nested element at `(outerIndex, innerIndex)`, accessing exactly
`(outerIndex, innerIndex)` returns the new value `val`.
-/
theorem getElem!_setNested_inner_self {α : Type u} [Inhabited α]
    (arr : Array (Array α)) (outerIndex innerIndex : Nat) (val : α)
    (hOuter : outerIndex < arr.size) (hInner : innerIndex < (arr[outerIndex]!).size) :
    ((setNested arr outerIndex innerIndex val hOuter hInner)[outerIndex]!)[innerIndex]! =
      val := by
  unfold setNested
  rw [getElem!_set_self arr outerIndex hOuter
    ((arr[outerIndex]!).set innerIndex val hInner)]
  exact getElem!_set_self (arr[outerIndex]!) innerIndex hInner val

/--
Swap the elements at indices `i` and `j` in array `a`.
-/
def arraySwapAt [Inhabited α] (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) : Array α :=
  let b := a.set i a[j]! hi
  b.set j a[i]! (by simpa [b, Array.size_set] using hj)

/--
Swapping two elements preserves array size.
-/
theorem size_arraySwapAt [Inhabited α] (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (arraySwapAt a i j hi hj).size = a.size := by
  simp [arraySwapAt, Array.size_set]

/--
After swapping elements at `i` and `j`, accessing `i` with `getElem!` returns
the original value at `j`.
-/
theorem getElem!_arraySwapAt_left [Inhabited α] (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (arraySwapAt a i j hi hj)[i]! = a[j]! := by
  by_cases hji : j = i
  · subst j
    simp [arraySwapAt, getElem!_set_self]
  · simp [arraySwapAt, hi, hj, hji, getElem!_set_self, getElem!_set_ne]

/--
After swapping elements at `i` and `j`, accessing `j` with `getElem!` returns
the original value at `i`.
-/
theorem getElem!_arraySwapAt_right [Inhabited α] (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (arraySwapAt a i j hi hj)[j]! = a[i]! := by
  simp [arraySwapAt, getElem!_set_self]

/--
After swapping elements at `i` and `j`, any other index `k` is unchanged.
-/
theorem getElem!_arraySwapAt_of_ne [Inhabited α] (a : Array α) (i j k : Nat)
    (hi : i < a.size) (hj : j < a.size) (hk : k < a.size) (hki : i ≠ k) (hkj : j ≠ k) :
    (arraySwapAt a i j hi hj)[k]! = a[k]! := by
  simp [arraySwapAt, hi, hj, hk, hki, hkj, getElem!_set_ne]

/--
Update element at index `i` using function `f`, then set element at index `j` to `second`.
Useful for patterns like `a[i] := f a[i]; a[j] := second`.
-/
def updateAtThenSet {α : Type _} (a : Array α) (i j : Nat)
    (f : α → α) (second : α) (hi : i < a.size) (hj : j < a.size) : Array α :=
  setTwoValues a i j (f (a[i]'hi)) second hi hj

theorem size_updateAtThenSet {α : Type _} (a : Array α) (i j : Nat)
    (f : α → α) (second : α) (hi : i < a.size) (hj : j < a.size) :
    (updateAtThenSet a i j f second hi hj).size = a.size := by
  unfold updateAtThenSet
  rw [size_setTwoValues]

theorem getElem!_updateAtThenSet_updated {α : Type _} [Inhabited α]
    (a : Array α) (i j : Nat) (f : α → α) (second : α)
    (hi : i < a.size) (hj : j < a.size) (hij : i ≠ j) :
    (updateAtThenSet a i j f second hi hj)[i]! = f a[i]! := by
  unfold updateAtThenSet
  rw [getElem!_setTwoValues_first _ _ _ _ _ _ _ hij,
    getElem!_eq_getElem_of_lt]

theorem getElem!_updateAtThenSet_of_ne {α : Type _} [Inhabited α]
    (a : Array α) (i j k : Nat) (f : α → α) (second : α)
    (hi : i < a.size) (hj : j < a.size) (hk : k < a.size)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (updateAtThenSet a i j f second hi hj)[k]! = a[k]! := by
  unfold updateAtThenSet
  exact getElem!_setTwoValues_of_ne a i j k (f (a[i]'hi)) second hi hj hk hki hkj

/--
For an index within bounds, mapping `f` over `a` and then accessing with
`getElem!` equals applying `f` to the corresponding element of `a`.
-/
theorem map_getElem! [Inhabited α] [Inhabited β]
    (f : α → β) (a : Array α) (i : Nat) (hi : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  simp [getElem!_pos, hi]

/--
Mapping `f` over an array preserves size, and for each index in bounds,
`(a.map f)[i]! = f a[i]!`. Convenience bundle of `Array.size_map` and
`map_getElem!` that is frequently needed when reasoning about mapped arrays.
-/
theorem map_size_and_getElem! [Inhabited α] [Inhabited β]
    (f : α → β) (a : Array α) :
    (a.map f).size = a.size ∧ ∀ i, i < a.size → (a.map f)[i]! = f a[i]! := by
  exact ⟨Array.size_map _ _, map_getElem! f a⟩

/--
Find the index of the first element satisfying predicate `p` in array `a`,
by delegating to `List.findIdx` on the underlying list.
-/
def firstMatchingIndex {α : Type} (p : α → Bool) (a : Array α) : Nat :=
  a.toList.findIdx p

/--
If there exists an element in `a` satisfying `p`, then `firstMatchingIndex p a`
is a valid index (< `a.size`), the element at that index satisfies `p`,
and no earlier element satisfies `p`.
-/
theorem firstMatchingIndex_spec {α : Type} [Inhabited α] {p : α → Bool} {a : Array α}
    (h : ∃ x ∈ a, p x) :
    firstMatchingIndex p a < a.size ∧
      p a[firstMatchingIndex p a]! = true ∧
      ∀ k, k < firstMatchingIndex p a → p a[k]! = false := by
  rcases h with ⟨x, hx_mem, hx_p⟩
  have hx_mem_list : x ∈ a.toList := by simpa using hx_mem
  have hx_p_eq : p x = true := by simpa using hx_p
  have h_bound : a.toList.findIdx p < a.toList.length := by
    rw [List.findIdx_lt_length]
    exact ⟨x, hx_mem_list, hx_p_eq⟩
  have hi_bound : a.toList.findIdx p < a.size := by simpa using h_bound
  have h_lt : firstMatchingIndex p a < a.size := by
    unfold firstMatchingIndex; exact hi_bound
  have h_val : p a[firstMatchingIndex p a]! = true := by
    unfold firstMatchingIndex
    rw [getElem!_pos a (a.toList.findIdx p) hi_bound]
    rw [← Array.getElem_toList hi_bound]
    have h_list_val : p (a.toList[a.toList.findIdx p]'h_bound) = true :=
      List.findIdx_getElem (w := h_bound)
    simpa using h_list_val
  have h_min : ∀ k, k < firstMatchingIndex p a → p a[k]! = false := by
    intro k hk
    unfold firstMatchingIndex at hk
    have hk_size : k < a.size :=
      lt_of_lt_of_le hk (by simpa using Nat.le_of_lt h_bound)
    rw [getElem!_pos a k hk_size]
    rw [← Array.getElem_toList hk_size]
    have h_eq := (List.findIdx_eq (h := h_bound)).mp rfl
    simpa using h_eq.2 k hk
  exact ⟨h_lt, h_val, h_min⟩

/--
For an index `i` within bounds of `arr.toList`, `arr[i]!` equals
the bounded-access `arr.toList[i]'hi`. Useful for translating between
array-element and list-element representations in proofs.
-/
theorem getElem!_eq_toList_getElem {α : Type _} [Inhabited α] {arr : Array α} {i : Nat}
    (hi : i < arr.toList.length) :
    arr[i]! = arr.toList[i]'hi := by
  have hiArr : i < arr.size := by
    simpa [Array.length_toList] using hi
  calc
    arr[i]! = arr[i] := by rw [getElem!_pos]
    _ = arr.toList[i]'hi := (Array.getElem_toList hiArr).symm

/--
If a predicate `p` holds for `arr.toList[i]` (with `i < arr.toList.length`),
then `p` holds for `arr[i]!`.
-/
theorem getElem!_satisfies_of_toList_pred {α : Type _} [Inhabited α]
    {arr : Array α} {p : α → Bool} {i : Nat}
    (hi : i < arr.toList.length) (hpred : p (arr.toList[i]'hi)) :
    p arr[i]! := by
  rwa [getElem!_eq_toList_getElem hi]

/--
Find the first index in array `a` where the element equals `target`,
using `BEq` for comparison. Returns `a.size` if `target` is not found.
-/
def firstEqualIndex {α : Type} [BEq α] (a : Array α) (target : α) : Nat :=
  firstMatchingIndex (fun x => x == target) a

/--
Find the first index in array `a` where the `DecidablePred` `p` holds.
Returns `some idx` if found, `none` otherwise. Uses `Nat.find` on the
existence proof to guarantee the returned index is minimal.

Unlike `firstMatchingIndex` (which uses `Bool` predicates and always
returns a `Nat`), this version works with `Prop` predicates and
explicitly signals absence via `Option`.
-/
def firstIndexWhere [Inhabited α] (a : Array α) (p : α → Prop) [DecidablePred p] : Option Nat :=
  if h : ∃ i, i < a.size ∧ p (a[i]!) then
    some (Nat.find h)
  else
    none

/--
If `firstIndexWhere a p` returns `some idx`, then `idx` is a valid index
strictly less than `a.size`, the element `a[idx]!` satisfies `p`, and no
earlier index satisfies `p` — i.e., `idx` is minimal.
-/
lemma firstIndexWhere_some_spec [Inhabited α] {a : Array α} {p : α → Prop} [DecidablePred p]
    (h : ∃ i, i < a.size ∧ p (a[i]!)) :
    let idx := Nat.find h
    idx < a.size ∧ p (a[idx]!) ∧
      (∀ j, j < idx → ¬ p (a[j]!)) := by
  dsimp
  have hfind := Nat.find_spec h
  refine ⟨hfind.1, hfind.2, ?_⟩
  intro j hj hodd
  exact Nat.find_min h hj ⟨Nat.lt_trans hj hfind.1, hodd⟩

/--
Specification for `firstIndexWhere`: in the `some idx` case, `idx` is
a minimal valid index; in the `none` case, no element satisfies `p`.
-/
lemma firstIndexWhere_spec [Inhabited α] (a : Array α) (p : α → Prop) [DecidablePred p] :
    match firstIndexWhere a p with
    | some idx =>
        idx < a.size ∧ p (a[idx]!) ∧
          (∀ j, j < idx → ¬ p (a[j]!))
    | none =>
        ∀ i, i < a.size → ¬ p (a[i]!) := by
  unfold firstIndexWhere
  by_cases h : ∃ i, i < a.size ∧ p (a[i]!)
  · rw [dif_pos h]
    exact firstIndexWhere_some_spec h
  · rw [dif_neg h]
    intro i hi hp
    exact h ⟨i, hi, hp⟩

/-!
# `findIdxWhere` – Prop-based first-index search returning `Nat`

`findIdxWhere p a` returns the first index `i` with `p (a[i]!)` (as a `Prop`),
or `a.size` if no element satisfies `p`. Uses `Nat.find` for the minimal-index
guarantee.

Unlike `firstIndexWhere` (which returns `Option Nat`), this version returns
a bare `Nat` with `a.size` as the sentinel for "not found" — convenient when
the result is used as an array index directly.

Unlike `firstMatchingIndex` (which uses `Bool` predicates), this version
accepts `p : α → Prop` with a `DecidablePred` instance.
-/

/--
Find the first index `i` in `a` such that `p (a[i]!)` holds (as a `Prop`),
returning that index, or `a.size` if no element satisfies `p`.

Uses `Nat.find` to guarantee the returned index is minimal.
-/
def findIdxWhere {α : Type u} [Inhabited α] (a : Array α) (p : α → Prop) [DecidablePred p] : Nat :=
  if h : ∃ i, i < a.size ∧ p a[i]! then Nat.find h else a.size

/--
Specification for `findIdxWhere a p`:
1. The result is ≤ `a.size`.
2. Either the result equals `a.size` (not found), or `p` holds at `a[result]!`.
3. No earlier index satisfies `p` (minimality).
-/
lemma findIdxWhere_spec {α : Type u} [Inhabited α] (a : Array α) (p : α → Prop) [DecidablePred p] :
    findIdxWhere a p ≤ a.size ∧
      (findIdxWhere a p = a.size ∨ p a[findIdxWhere a p]!) ∧
      (∀ i, i < findIdxWhere a p → ¬ p a[i]!) := by
  unfold findIdxWhere
  by_cases h : ∃ i, i < a.size ∧ p a[i]!
  · rw [dif_pos h]
    have hfind := Nat.find_spec h
    refine ⟨Nat.le_of_lt hfind.1, Or.inr hfind.2, ?_⟩
    intro i hi hp
    exact Nat.find_min h hi ⟨Nat.lt_trans hi (Nat.find_spec h).1, hp⟩
  · rw [dif_neg h]
    refine ⟨by rfl, Or.inl rfl, ?_⟩
    intro i hi hp
    exact h ⟨i, hi, hp⟩

/--
`i` is in the half-open window `[start, start + len)`.
-/
def inWindow (start len i : Nat) : Prop :=
  start ≤ i ∧ i < start + len

instance inWindowDecidable (start len i : Nat) : Decidable (inWindow start len i) := by
  unfold inWindow
  infer_instance

/--
For an array overwrite operation, determine the value at index `idx`:
if `idx` falls within `[destStart, destStart + len)`, take from `src`;
otherwise keep the existing `dest` value.
-/
def overwriteValueAt [Inhabited α] (src : Array α) (srcStart : Nat)
    (dest : Array α) (destStart len : Nat) (idx : Fin dest.size) : α :=
  if inWindow destStart len idx.val then
    src[srcStart + (idx.val - destStart)]!
  else
    dest[idx.val]!

/--
Overwrite a contiguous range of `dest` starting at `destStart` with `len` elements
from `src` starting at `srcStart`. Returns a new array of size `dest.size`.
-/
def overwriteRange [Inhabited α] (src : Array α) (srcStart : Nat)
    (dest : Array α) (destStart len : Nat) : Array α :=
  Array.ofFn fun (idx : Fin dest.size) =>
    overwriteValueAt src srcStart dest destStart len idx

/--
The size of `overwriteRange` equals the size of the destination array.
-/
theorem overwriteRange_size [Inhabited α] (src : Array α) (srcStart : Nat)
    (dest : Array α) (destStart len : Nat) :
    (overwriteRange src srcStart dest destStart len).size = dest.size := by
  simp [overwriteRange]

/--
After the overwrite range, the overwritten array matches the original destination.
-/
theorem overwriteRange_get_after [Inhabited α] (src : Array α) (srcStart : Nat)
    (dest : Array α) (destStart len : Nat) (i : Nat) (hi : destStart + len ≤ i)
    (hiSize : i < (overwriteRange src srcStart dest destStart len).size) :
    (overwriteRange src srcStart dest destStart len)[i]! = dest[i]! := by
  have hiDestSize : i < dest.size := by
    rwa [overwriteRange_size] at hiSize
  unfold overwriteRange
  rw [getElem!_pos
    (h := by
      simpa [Array.size_ofFn] using hiDestSize)]
  rw [Array.getElem_ofFn]
  have hNotInSegment : ¬ inWindow destStart len i := by
    unfold inWindow
    omega
  simp [overwriteValueAt, hNotInSegment]

/--
Within the overwrite range, the overwritten array matches the source.
-/
theorem overwriteRange_get_inside [Inhabited α] (src : Array α) (srcStart : Nat)
    (dest : Array α) (destStart len : Nat)
    (hDestRange : destStart + len ≤ dest.size)
    (i : Nat) (hi : i < len) :
    (overwriteRange src srcStart dest destStart len)[destStart + i]! =
      src[srcStart + i]! := by
  have hiDestSize : destStart + i < dest.size := by
    omega
  unfold overwriteRange
  rw [getElem!_pos
    (h := by
      simpa [Array.size_ofFn] using hiDestSize)]
  rw [Array.getElem_ofFn]
  have hInSegment : inWindow destStart len (destStart + i) := by
    unfold inWindow
    omega
  simp [overwriteValueAt, hInSegment, Nat.add_sub_cancel_left]

/--
Count elements in array `a` satisfying boolean predicate `p`.
Simple zero-starting count with `Bool` predicates; see `foldlCountFrom`
for counting from an arbitrary start value or for `Prop`-based predicates.
-/
@[inline]
def countBy {α : Type u} (p : α → Bool) (a : Array α) : Nat :=
  a.foldl (fun cnt x => if p x then cnt + 1 else cnt) 0

/--
A step function for counting elements that satisfy a predicate.
Increments the accumulator `count` by 1 when `p x` holds,
leaves it unchanged otherwise.
-/
def countStep {α : Type u} (p : α → Prop) [DecidablePred p] (count : Nat) (x : α) : Nat :=
  if p x then count + 1 else count

/--
Fold over an array from the left, counting how many elements satisfy predicate `p`.
Starts from the given `start` count so it can be chained across multiple
arrays or segments, or used to resume a partial count.

See also `countBy` for the simpler `Bool`-predicate version counting from zero.
-/
def foldlCountFrom {α : Type u} (p : α → Prop) [DecidablePred p] (start : Nat) (xs : Array α) : Nat :=
  xs.foldl (countStep p) start

/--
If `firstIdxOf a.toList key` returns `some idx`, then `idx` is within bounds of `a`,
`a[idx]! = key`, and no earlier index in `a` equals `key`.

This lifts `List.firstIdxWhere_some_spec` from the list representation to the array via
`getElem!_toList`.
-/
lemma firstIdxOf_toList_some_spec {α : Type u} [DecidableEq α] [Inhabited α]
    {a : Array α} {key : α} {idx : Nat} (h : List.firstIdxOf a.toList key = some idx) :
    idx < a.size ∧ a[idx]! = key ∧ ∀ j : Nat, j < idx → a[j]! ≠ key := by
  have hspec := List.firstIdxWhere_some_spec (xs := a.toList) (p := fun x => x = key) h
  have h_bound : idx < a.toList.length := hspec.1
  constructor
  · rwa [Array.size_eq_length_toList]
  constructor
  · have harr_eq := getElem!_toList a idx h_bound
    rw [harr_eq]
    exact hspec.2.1
  · intro j hj
    have hj_bound : j < a.toList.length := Nat.lt_trans hj h_bound
    have harr_eq := getElem!_toList a j hj_bound
    rw [harr_eq]
    exact hspec.2.2 j hj

/--
For an index `i` within bounds of `xs.extract start stop`, accessing with
`getElem!` on the extracted subarray equals accessing the original array
at index `i + start` with `getElem!`.
-/
theorem getElem!_extract_eq_getElem! {α : Type u} [Inhabited α]
    (xs : Array α) (start stop i : Nat)
    (h : i < (xs.extract start stop).size) :
    (xs.extract start stop)[i]! = xs[i + start]! := by
  have h_src : i + start < xs.size := by
    have h_size : i < min stop xs.size - start := by
      simpa [Array.size_extract] using h
    omega
  rw [getElem!_pos (xs.extract start stop) i h]
  rw [getElem!_pos xs (i + start) h_src]
  rw [Array.getElem_extract h]
  congr 1
  omega

/--
`getElem!` on an `Array.ofFn` reduces to the underlying function application
when the index is in bounds.
-/
theorem getElem!_ofFn {α : Type} [Inhabited α] {n : Nat}
    (f : Fin n → α) {i : Nat} (h : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  have hs : i < (Array.ofFn f).size := by simpa using h
  rw [getElem!_pos (Array.ofFn f) i hs]
  rw [Array.getElem_ofFn]

/--
Reindex an array: produce a new array of the same size where the element at
position `i` is `a[index i]!` (using `getElem!` for out-of-bounds safety).
-/
def reindex {α : Type} [Inhabited α] (index : Nat → Nat) (a : Array α) : Array α :=
  Array.ofFn (fun i : Fin a.size => a[index i.val]!)

/--
Reindexing preserves array size.
-/
theorem reindex_size {α : Type} [Inhabited α] (index : Nat → Nat) (a : Array α) :
    (reindex index a).size = a.size := by
  unfold reindex
  simp

/--
Accessing a reindexed array at position `i` (with `i` in bounds of the original)
equals the original array at the remapped index.
-/
theorem getElem!_reindex {α : Type} [Inhabited α] (index : Nat → Nat) (a : Array α) :
    ∀ i : Nat, i < a.size → (reindex index a)[i]! = a[index i]! := by
  intro i hi
  unfold reindex
  rw [getElem!_ofFn _ hi]

/-! ## Sorting

Sort an array by a relation `r` using merge sort on the underlying list.
-/

/-- Sort an array by a relation `r`, using merge sort on the underlying list. -/
def sortByRel {α : Type u} (r : α → α → Prop) [DecidableRel r] (a : Array α) : Array α :=
  (List.sortByRel r a.toList).toArray

/-- Sorting an array by `r` and converting to list yields a list that is pairwise ordered by `r`. -/
theorem sortByRel_pairwise_toList {α : Type u} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : Array α) :
    List.Pairwise r (sortByRel r a).toList := by
  simpa [sortByRel, List.sortByRel, List.Sorted] using (List.sorted_mergeSort' r a.toList)

/--
For an array `a` with index `i` in bounds, accessing the `i`-th element
of `a.toList.map f` (with bounded `getElem`) equals `f` applied to
`a[i]` (also bounded). Generalizes `mapped_array_row_toList`.
-/
theorem toList_map_getElem {α β : Type u} (a : Array α) (f : α → β) {i : Nat}
    (hi : i < a.size) :
    (a.toList.map f)[i]'(by simpa using hi) = f (a[i]'hi) := by
  rw [List.getElem_map]
  exact congrArg f (Array.getElem_toList hi)

end Array

/-!
# List ↔ Array conversion

Bundled lemmas bridging `List.toArray` properties that are commonly needed
when converting between list and array representations.
-/

namespace List

/--
Converting a list to an array preserves both size and element-wise access
(via `get!`). This bundles `List.size_toArray` and `List.getElem!_toArray`
into a single conjunction, which is convenient when bridging list and array
proofs — the size equality lets you translate length bounds to size bounds,
and the element equality lets you substitute `toArray` accesses.
-/
theorem toArray_size_and_getElem! {α : Type u} [Inhabited α] (xs : List α) :
    xs.toArray.size = xs.length ∧
      ∀ (i : Nat), i < xs.length → xs.toArray[i]! = xs[i]! := by
  constructor
  · exact List.size_toArray xs
  · intro i _h_bounds
    simp

end List

end Specific
