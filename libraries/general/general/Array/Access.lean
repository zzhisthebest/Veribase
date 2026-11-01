import Mathlib

namespace Array


/-! ### Index-weighted sum -/

/-- Weighted sum `Σ_{i=0}^{n-1} i * arr[i]` of the first `n` elements.
Each element is multiplied by its index before summing. -/
def weightedSum (arr : Array Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + i * arr[i]!) 0



/-! ### Sum of array entries at a given list of indices -/

/-- Sum the array entries at the given list of indices.
Unlike `subarraySum` (which sums a contiguous range), this works with
any (possibly non-contiguous) index list. -/
def arraySumAtIndices (arr : Array Nat) (indices : List Nat) : Nat :=
  indices.foldl (fun acc i => acc + arr[i]!) 0

lemma arraySumAtIndices_nil (arr : Array Nat) : arraySumAtIndices arr [] = 0 := by
  simp [arraySumAtIndices]

lemma arraySumAtIndices_cons (arr : Array Nat) (i : Nat) (is : List Nat) :
    arraySumAtIndices arr (i :: is) = arr[i]! + arraySumAtIndices arr is := by
  simp [arraySumAtIndices]
  have helper : ∀ (x : Nat), List.foldl (fun acc i' => acc + arr[i']!) x is = x + List.foldl (fun acc i' => acc + arr[i']!) 0 is := by
    intro x
    induction is generalizing x with
    | nil => simp
    | cons j js ih =>
      simp [List.foldl_cons, add_zero]
      rw [ih (x + arr[j]!), ih arr[j]!, add_assoc]
  simpa [List.foldl_cons, add_zero] using helper (arr[i]!)

lemma arraySumAtIndices_singleton (arr : Array Nat) (i : Nat) :
    arraySumAtIndices arr [i] = arr[i]! := by
  simp [arraySumAtIndices]


end Array

namespace Array


/-! ### `getElem!` equivalence — connecting `!`-indexing to `getElem` with bounds proof -/

/-- `a[i]!` equals `a[i]'h` when the index `i` is known to be in bounds.
This bridges the unsafe `!` notation (which returns `default` on out-of-bounds)
to the safe `getElem` (which requires a proof of in-bounds access). -/
theorem getElem!_eq_getElem (a : Array α) [Inhabited α] (i : Nat) (h : i < a.size) :
    a[i]! = a[i]'h := by
  simp [GetElem?.getElem!, Array.get!Internal, Array.getD, h]

/-- `a[i]! = a[i]` when the index `i` is in bounds. This is the implicit-proof
variant of `getElem!_eq_getElem`, using `a[i]` (which synthesizes the bounds proof
from `h`) instead of `a[i]'h`. Matches the `List.getElem!_eq_getElem_of_lt` API. -/
lemma getElem!_eq_getElem_of_lt {α : Type _} [Inhabited α] {a : Array α} {i : Nat} (h : i < a.size) :
    a[i]! = a[i] := by
  simpa using getElem!_eq_getElem a i h

/-- `a[i]?.getD d = a[i]` when the index `i` is known to be in bounds.
This bridges the `getElem?`/`getD` pattern (which returns a default `d` on out-of-bounds)
to the safe `getElem` (which requires a proof of in-bounds access). When `i < a.size`,
the default `d` is irrelevant — the value is always `a[i]`. -/
theorem getElem?_getD_eq [Zero α] (a : Array α) (d : α) (i : Nat) (hi : i < a.size) :
    a[i]?.getD d = a[i] := by
  have h := Array.getElem?_eq_getElem hi
  rw [h, Option.getD_some]

/-- Nested version of `getElem!_eq_getElem`: for a 2D array `a`, when both indices
`i` and `j` are in bounds, the double-`!` access `(a[i]!)[j]!` equals the safe
double-access `(a[i])[j]`. -/
theorem nested_getElem!_eq_getElem {α : Type} [Inhabited α] (a : Array (Array α)) (i j : Nat)
    (hi : i < a.size) (hj : j < (a[i]).size) : (a[i]!)[j]! = (a[i])[j] := by
  have h1 : a[i]! = a[i] := by simpa using getElem!_eq_getElem a i hi
  have h2 : (a[i])[j]! = (a[i])[j] := by simpa using getElem!_eq_getElem (a[i]) j hj
  calc
    (a[i]!)[j]! = (a[i])[j]! := by rw [h1]
    _ = (a[i])[j] := by rw [h2]

/-! ### `getElem!` across List↔Array conversion -/

/-- `(xs : List α).toArray[i]! = xs[i]!` when `i` is in bounds.
This bridges `!`-indexing from `Array` to `List` via `List.toArray`. -/
theorem getElem!_list_toArray {α : Type} [Inhabited α] (xs : List α) (i : Nat)
    (hi : i < xs.length) : xs.toArray[i]! = xs[i]! := by
  have hi_arr : i < xs.toArray.size := by simpa [List.size_toArray] using hi
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  simp [hi_arr, List.getElem_toArray hi_arr]

/-- `(xs : Array α).toList[i]! = xs[i]!` when `i` is in bounds.
This bridges `!`-indexing from `List` to `Array` via `Array.toList`. -/
theorem getElem!_toList {α : Type} [Inhabited α] (xs : Array α) (i : Nat)
    (hi : i < xs.size) : xs.toList[i]! = xs[i]! := by
  rcases xs with ⟨xs⟩
  simp

/-- `(Array.mk l)[i.val]! = l.get i` for `i : Fin l.length`.
This bridges `!`-indexing on `Array.mk` with `List.get`,
tying together the Array and List indexing APIs. -/
theorem mk_getElem!_eq {α : Type} [Inhabited α] (l : List α) (i : Fin l.length) :
    (Array.mk l)[i.val]! = l.get i := by
  have hi_lt : i.val < (Array.mk l).size := by
    simpa using i.2
  rw [getElem!_pos (Array.mk l) i.val hi_lt]
  simp

/-- `Array.map` distributes over `!`-indexing:
`(arr.map f)[i]! = f (arr[i]!)` when `i` is in bounds.
This is the unsafe-indexing counterpart of `Array.getElem_map`. -/
theorem map_getElem!_eq (f : α → β) (arr : Array α) (i : Nat) (h : i < arr.size) [Inhabited α] [Inhabited β] :
    (arr.map f)[i]! = f (arr[i]!) := by
  have hmap : i < (arr.map f).size := by simpa [Array.size_map] using h
  calc
    (arr.map f)[i]! = (arr.map f)[i]'hmap := getElem!_eq_getElem _ _ hmap
    _ = f (arr[i]'h) := Array.getElem_map f arr i hmap
    _ = f (arr[i]!) := by rw [getElem!_eq_getElem arr i h]

/-- `Array.mapIdx` distributes over `!`-indexing:
`(xs.mapIdx f)[i]! = f i (xs[i]!)` when `i` is in bounds.
This is the unsafe-indexing counterpart of `Array.getElem_mapIdx`. -/
theorem getElem!_mapIdx_of_lt {α β : Type} [Inhabited α] [Inhabited β]
    (f : Nat → α → β) (xs : Array α) (i : Nat) (h : i < xs.size) :
    (xs.mapIdx f)[i]! = f i (xs[i]!) := by
  have hsize : (xs.mapIdx f).size = xs.size := by simp
  have hi' : i < (xs.mapIdx f).size := by rw [hsize]; exact h
  have hresult_pos : (xs.mapIdx f)[i]! = (xs.mapIdx f)[i]'hi' :=
    getElem!_eq_getElem _ _ hi'
  have hxs_get : xs[i]! = xs[i]'h :=
    getElem!_eq_getElem _ _ h
  have h_map_val : (xs.mapIdx f)[i]'hi' = f i (xs[i]'h) := by
    simpa using Array.getElem_mapIdx f xs i hi'
  rw [hresult_pos, h_map_val, ← hxs_get]

/-! ### `get!` on `ofFn` — evaluate indexed access with bounds proof -/

/-- Evaluate `(Array.ofFn f)[i]!` when the index `i` is known to be in bounds.
This combines several `simp` lemmas into a single useful form. -/
theorem get_bang_ofFn {α : Type _} [Inhabited α] {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  have hi_size : i < (Array.ofFn f).size := by
    simpa [Array.size_ofFn] using hi
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi_size,
    Array.getElem_ofFn f i hi_size]

/-- `(Array.ofFn f)[i.val]! = f i` for `i : Fin n`.
This is the `Fin`-based variant of `get_bang_ofFn`, more ergonomic when the index
is already given as a `Fin n`. -/
theorem ofFn_getElem!_eq {α : Type _} [Inhabited α] {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  simpa [Fin.eta] using get_bang_ofFn f i.val i.2

/-! ### Nested `ofFn` — 2D array construction via `Array.ofFn` -/

/-- For a 2D array constructed via nested `Array.ofFn`, the size of each row equals `m`.
This is the row-size counterpart of `Array.get_bang_ofFn` for 2D arrays. -/
theorem nested_ofFn_row_size {n m : Nat} {α : Type _} (f : Fin n → Fin m → α) (i : Nat) (hi : i < n) :
    ((Array.ofFn (fun (i' : Fin n) => Array.ofFn (fun (j : Fin m) => f i' j)))[i]!).size = m := by
  have hi_arr : i < (Array.ofFn (fun (i' : Fin n) => Array.ofFn (fun (_j : Fin m) => f i' _j))).size := by
    simpa [Array.size_ofFn] using hi
  rw [getElem!_pos _ i hi_arr]
  rw [Array.getElem_ofFn (fun (i' : Fin n) => Array.ofFn (fun (j : Fin m) => f i' j)) i hi_arr]
  simp [Array.size_ofFn]

/-- Accessing element `[i][j]` of a 2D array built via nested `Array.ofFn` gives `f ⟨i, hi⟩ ⟨j, hj⟩`.
This is the 2D generalization of `Array.get_bang_ofFn`. -/
theorem nested_ofFn_get {n m : Nat} {α : Type _} [Inhabited α] (f : Fin n → Fin m → α) (i j : Nat) (hi : i < n) (hj : j < m) :
    (((Array.ofFn (fun (i' : Fin n) => Array.ofFn (fun (j' : Fin m) => f i' j')))[i]!)[j]!) = f ⟨i, hi⟩ ⟨j, hj⟩ := by
  have houter := get_bang_ofFn (fun (i' : Fin n) => Array.ofFn (fun (j' : Fin m) => f i' j')) i hi
  rw [houter]
  have hinner := get_bang_ofFn (fun (j' : Fin m) => f ⟨i, hi⟩ j') j hj
  rw [hinner]

/-! ### Array from `(List.range n).map f).toArray` — array built from range mapping -/

/-- The size of an array constructed by mapping a function `f` over `List.range n`
and converting to an `Array` equals `n`. -/

theorem size_range_map_toArray (n : Nat) (f : Nat → α) : ((List.range n).map f).toArray.size = n := by
  simp

/-- Accessing `((List.range n).map f).toArray[i]!` equals `f i` when `i < n`.
This is the `!`-indexing counterpart of `Array.getElem_ofFn` for the
`toArray` construction pattern from a list range. -/
theorem get_bang_range_map_toArray (n : Nat) (f : Nat → α) (i : Nat) (hi : i < n) [Inhabited α] :
    ((List.range n).map f).toArray[i]! = f i := by
  simp [hi]


end Array
