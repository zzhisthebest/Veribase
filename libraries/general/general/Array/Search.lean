import Mathlib
import general.Array.Access
import general.List.Find

namespace Array


/-! ### Index search within bounds -/

/--
`anyIdxFrom arr pred start` returns `true` iff there exists an index `i` with
`start ≤ i < arr.size` such that `pred i = true`.
-/
def anyIdxFrom {α : Type} (arr : Array α) (pred : Nat → Bool) (start : Nat) : Bool :=
  if h : start < arr.size then
    if pred start then true else anyIdxFrom arr pred (start + 1)
  else
    false
termination_by arr.size - start
decreasing_by
  omega

/--
Correctness of `anyIdxFrom`: returns `true` iff there exists an index `j` with
`start ≤ j < arr.size` such that `pred j = true`.
-/
theorem anyIdxFrom_spec {α : Type} (arr : Array α) (pred : Nat → Bool) (start : Nat) :
    (anyIdxFrom arr pred start = true) ↔
    ∃ j, start ≤ j ∧ j < arr.size ∧ pred j := by
  have h_aux : ∀ (meas : Nat), (∀ (k : Nat), arr.size - k = meas →
      ((anyIdxFrom arr pred k = true) ↔
       (∃ j, k ≤ j ∧ j < arr.size ∧ pred j))) := by
    intro meas
    refine Nat.strong_induction_on meas ?_
    intro m IH k hk_eq
    unfold anyIdxFrom
    split
    · rename_i hk_lt
      split
      · rename_i hpred
        simp
        exact ⟨k, le_refl k, hk_lt, hpred⟩
      · rename_i hpred
        have hlt : arr.size - (k + 1) < m := by
          rw [← hk_eq]
          omega
        have hrec := IH (arr.size - (k + 1)) hlt (k + 1) rfl
        rw [hrec]
        constructor
        · intro ⟨j, hkj, hj_lt, hpred_j⟩
          exact ⟨j, Nat.le_trans (Nat.le_succ k) hkj, hj_lt, hpred_j⟩
        · intro ⟨j, hkj, hj_lt, hpred_j⟩
          by_cases h_eq : j = k
          · subst h_eq; exact absurd hpred_j hpred
          · have hk1j : k + 1 ≤ j := by omega
            exact ⟨j, hk1j, hj_lt, hpred_j⟩
    · rename_i hk_not_lt
      constructor
      · intro h; simp at h
      · intro ⟨j, hkj, hj_lt, _⟩; omega
  exact h_aux (arr.size - start) start rfl


/-! ### Find all indices where predicate holds -/

/-- Return the list of all indices `i` where `p (as[i]!)` holds, in increasing order.
This returns *all* matching indices, unlike `findFirstIdx` which returns only the first.
Uses `!`-indexing with an `Inhabited` default. -/
def indicesWhere {α : Type} [Inhabited α] (as : Array α) (p : α → Bool) : List Nat :=
  (List.range as.size).filter (fun i => p (as[i]!))

/-- `indicesWhere` always produces a list with no duplicates. -/
lemma indicesWhere_nodup {α : Type} [Inhabited α] (as : Array α) (p : α → Bool) :
    List.Nodup (indicesWhere as p) := by
  unfold indicesWhere
  have h := List.nodup_range as.size
  exact h.filter (fun i => p (as[i]!))

/-- Membership in `indicesWhere` is equivalent to the index being in-bounds
and the predicate holding at that index. -/
lemma mem_indicesWhere_iff {α : Type} [Inhabited α] (as : Array α) (p : α → Bool) (i : Nat) :
    i ∈ indicesWhere as p ↔ i < as.size ∧ p (as[i]!) := by
  unfold indicesWhere
  simp


/-! ### `indicesOf` — find all indices where array element equals a value

`indicesOf` is the equality-specialized counterpart of `indicesWhere`: it uses `?` indexing
(no `Inhabited` required) to list all indices `i` where `arr[i]? = some x`.
The result is always sorted in ascending order. -/

/-- Find all indices in an array where the element equals a given value.
Uses `arr[i]?` (Option-based) indexing, so it does not require `Inhabited α`.
The result is sorted in ascending order.

Contrast with `indicesWhere`, which uses `!` indexing and requires `Inhabited α`. -/
def indicesOf (arr : Array α) (x : α) [DecidableEq α] : List Nat :=
  (List.range arr.size).filter (λ i => decide (arr[i]? = some x))

/-- For an array `arr` and a value `x`, an index `i` (within bounds) belongs to
`arr.indicesOf x` if and only if `arr[i]? = some x`. -/
lemma mem_indicesOf_iff {arr : Array α} {x : α} [DecidableEq α] {i : Nat} (h : i < arr.size) :
    (i ∈ arr.indicesOf x) ↔ arr[i]? = some x := by
  unfold indicesOf
  constructor
  · intro hmem; rcases List.mem_filter.1 hmem with ⟨_, hd⟩; exact of_decide_eq_true hd
  · intro heq; rw [List.mem_filter]; exact ⟨List.mem_range.2 h, decide_eq_true heq⟩

/-- The result of `arr.indicesOf x` is always sorted (ascending). -/
lemma sorted_indicesOf (arr : Array α) (x : α) [DecidableEq α] : List.Sorted (· ≤ ·) (arr.indicesOf x) := by
  unfold indicesOf
  apply List.Pairwise.filter
  exact List.sorted_le_range arr.size


/-! ### Find first index matching a predicate -/

/-- Scan forward from `start` to find the first index `i ≥ start` where `p i arr[i]!` is true.
    Returns `some i` if found, or `none` if no such index exists. -/
def findFirstIdx [Inhabited α] (arr : Array α) (start : Nat) (p : Nat → α → Bool) : Option Nat :=
  if h : start < arr.size then
    if p start arr[start]! then some start
    else findFirstIdx arr (start + 1) p
  else none
termination_by arr.size - start

lemma findFirstIdx_spec_aux [Inhabited α] (arr : Array α) (p : Nat → α → Bool) (start d : Nat)
    (hd : arr.size - start = d) :
    (findFirstIdx arr start p = none ∧ ∀ j, start ≤ j → j < arr.size → p j arr[j]! = false) ∨
    (∃ k, start ≤ k ∧ k < arr.size ∧ p k arr[k]! = true ∧
      findFirstIdx arr start p = some k ∧
      ∀ j, start ≤ j → j < k → p j arr[j]! = false) := by
  induction d using Nat.strong_induction_on generalizing start with
  | h d ih =>
    unfold findFirstIdx
    split
    · rename_i h_lt
      split
      · rename_i h_eq
        right
        refine ⟨start, ?_, h_lt, h_eq, rfl, ?_⟩
        · exact Nat.le_refl start
        · intro j h_sj h_js
          omega
      · rename_i h_ne
        have h_false : p start arr[start]! = false := by
          simpa using h_ne
        have h_sub_lt : arr.size - (start + 1) < d := by
          rw [← hd]
          omega
        have h_eq_next : arr.size - (start + 1) = arr.size - (start + 1) := rfl
        have h_rec := ih (arr.size - (start + 1)) h_sub_lt (start + 1) h_eq_next
        rcases h_rec with (⟨h_res_none, h_all_none⟩ | ⟨k, h_sk, h_k_lt, h_k_eq, h_res_k, h_all_k⟩)
        · left
          constructor
          · simpa [h_lt] using h_res_none
          · intro j h_sj h_j_lt
            by_cases h_js : j = start
            · subst h_js; exact h_false
            · have h_s1j : start + 1 ≤ j := by omega
              exact h_all_none j h_s1j h_j_lt
        · right
          refine ⟨k, ?_, h_k_lt, h_k_eq, ?_, ?_⟩
          · omega
          · simpa [h_lt] using h_res_k
          · intro j h_sj h_jk
            by_cases h_js : j = start
            · subst h_js; exact h_false
            · have h_s1j : start + 1 ≤ j := by omega
              exact h_all_k j h_s1j h_jk
    · rename_i h_not_lt
      left
      constructor
      · rfl
      · intro j h_sj h_j_lt
        have : arr.size ≤ start := by omega
        have : arr.size ≤ j := Nat.le_trans this h_sj
        omega

lemma findFirstIdx_spec [Inhabited α] (arr : Array α) (p : Nat → α → Bool) (start : Nat) :
    (findFirstIdx arr start p = none ∧ ∀ j, start ≤ j → j < arr.size → p j arr[j]! = false) ∨
    (∃ k, start ≤ k ∧ k < arr.size ∧ p k arr[k]! = true ∧
      findFirstIdx arr start p = some k ∧
      ∀ j, start ≤ j → j < k → p j arr[j]! = false) :=
  findFirstIdx_spec_aux arr p start (arr.size - start) rfl

/-- If `findFirstIdx arr 0 p` returns `some i`, then `i` is in bounds,
`p i arr[i]!` is true, and `p` is false at all indices `j < i`.
This specializes `findFirstIdx_spec` to the common `start = 0` case. -/
lemma findFirstIdx_zero_some_imp [Inhabited α] {arr : Array α} {p : Nat → α → Bool} {i : Nat}
    (h : findFirstIdx arr 0 p = some i) :
    i < arr.size ∧ p i arr[i]! = true ∧ ∀ j, j < i → p j arr[j]! = false := by
  rcases findFirstIdx_spec arr p 0 with (⟨h_none, _⟩ | ⟨k, _, h_k_lt, h_k_eq, h_res, h_min⟩)
  · rw [h_none] at h; simp at h
  · rw [h_res] at h
    have hk_eq_i : k = i := by simpa using h
    subst hk_eq_i
    exact ⟨h_k_lt, h_k_eq, fun j hj => h_min j (Nat.zero_le j) hj⟩

/-- If `findFirstIdx arr 0 p` returns `none`, then `p` is false at every valid index.
This specializes `findFirstIdx_spec` to the common `start = 0` case. -/
lemma findFirstIdx_zero_none_imp_all_false [Inhabited α] {arr : Array α} {p : Nat → α → Bool}
    (h : findFirstIdx arr 0 p = none) (i : Nat) (hi : i < arr.size) :
    p i arr[i]! = false := by
  rcases findFirstIdx_spec arr p 0 with (⟨_, h_all⟩ | ⟨_, _, _, _, h_res, _⟩)
  · exact h_all i (Nat.zero_le i) hi
  · rw [h_res] at h; simp at h

/-- If an element `x` is in `arr.toList` and satisfies the predicate `p`,
then `arr.find? p` is not `none`. This is the array counterpart of
`List.find?_ne_none_of_mem_pred`. -/
lemma find?_ne_none_of_mem_pred {α : Type} (p : α → Bool) (arr : Array α) (x : α)
    (h_mem : x ∈ arr.toList) (h_pred : p x = true) : arr.find? p ≠ none := by
  rw [← Array.find?_toList]
  exact List.find?_ne_none_of_mem_pred p arr.toList x h_mem h_pred

/-- The first element (index `0`) of a nonempty array belongs to its `toList`.
This connects array `getElem` at index 0 to list membership. -/
lemma getElem_zero_mem_toList {α : Type} (a : Array α) (h : a.size > 0) : a[0] ∈ a.toList := by
  have hmem_arr := Array.getElem_mem (xs := a) (i := 0) h
  exact (Array.mem_toList (a := a[0]) (xs := a)).mpr hmem_arr

/-! ### Find first index greater than a target -/

/-- Scan forward from `start` to find the first index `i ≥ start` where `arr[i]! > target`.
Returns `some i` if found, or `none` if no such index exists.

Uses a decidable `LinearOrder` (via `>` in the `if` condition), in contrast to
`findFirstIdx` which takes an explicit `Bool` predicate. This is the more idiomatic
version when the condition is a simple order comparison. -/
def firstGreaterIdx {α : Type} [LinearOrder α] [Inhabited α] (arr : Array α) (target : α) (start : Nat) : Option Nat :=
  if h : start < arr.size then
    if arr[start]! > target then
      some start
    else
      firstGreaterIdx arr target (start + 1)
  else
    none
termination_by arr.size - start

/-- If `firstGreaterIdx arr target start = none`, then every element from `start` onward
is `≤ target`. This is the correctness lemma for the "not found" case. -/
lemma firstGreaterIdx_none_spec {α : Type} [LinearOrder α] [Inhabited α] (arr : Array α) (target : α) (start : Nat)
    (h : firstGreaterIdx arr target start = none) :
    ∀ k, start ≤ k → k < arr.size → arr[k]! ≤ target := by
  intro k hle hklt
  unfold firstGreaterIdx at h
  split at h
  · rename_i hsize
    split at h
    · rename_i hcmp
      simp at h
    · rename_i hnot
      have h_ih := firstGreaterIdx_none_spec arr target (start + 1) h
      by_cases hkeq : k = start
      · subst hkeq; exact le_of_not_gt hnot
      · have h_ge : start + 1 ≤ k := by
          have hlt : start < k := Nat.lt_of_le_of_ne hle (Ne.symm hkeq)
          exact Nat.succ_le_of_lt hlt
        exact h_ih k h_ge hklt
  · rename_i hnsize
    have hnle : ¬ start ≤ k := by
      have hge : arr.size ≤ start := Nat.ge_of_not_lt hnsize
      have : k < start := Nat.lt_of_lt_of_le hklt hge
      exact Nat.not_le.mpr this
    exact absurd hle hnle
termination_by arr.size - start


/-! ### Find first element satisfying a predicate (value-returning) -/

/-- Find the first element in an array satisfying a predicate, starting from index `i`.
Returns `default` if no such element exists.

This is the value-returning counterpart of `findFirstIdx`, which returns the index.
Use `findFirstIdx` when you need the position; use `findFirstAux` when you need the value. -/
def findFirstAux [Inhabited α] (arr : Array α) (p : α → Bool) (i : Nat) : α :=
  if h : i < arr.size then
    if p (arr[i]) then
      arr[i]
    else
      findFirstAux arr p (i + 1)
  else
    default
termination_by arr.size - i
decreasing_by
  omega

/-- Specification for `Array.findFirstAux`: starting from index `i`, it returns the first
element in `arr` satisfying predicate `p`, or `default` if no such element exists. -/
lemma findFirstAux_spec [Inhabited α] (arr : Array α) (p : α → Bool) (i : Nat) :
    ((findFirstAux arr p i = default ∧
      (∀ j, i ≤ j → j < arr.size → p (arr[j]!) = false)) ∨
    (∃ k, i ≤ k ∧ k < arr.size ∧ (arr[k]!) = findFirstAux arr p i ∧
      p (findFirstAux arr p i) = true ∧
      (∀ j, i ≤ j → j < k → p (arr[j]!) = false))) := by
  unfold findFirstAux
  by_cases hi : i < arr.size
  · rw [dif_pos hi]
    by_cases hp : p (arr[i]) = true
    · rw [if_pos hp]
      right
      have h_bound : (arr[i]!) = arr[i] := by
        simp [getElem!_eq_getElem arr i hi]
      have h_forall : ∀ j, i ≤ j → j < i → p (arr[j]!) = false := by
        intro j hij hj_lt; omega
      exact ⟨i, Nat.le_refl i, hi, h_bound, hp, h_forall⟩
    · rw [if_neg hp]
      have h_ih := findFirstAux_spec arr p (i + 1)
      rcases h_ih with (⟨h_empty, h_all⟩ | ⟨k, hk_i, hk_sz, hk_eq, hk_pal, hk_all⟩)
      · left
        refine ⟨h_empty, ?_⟩
        intro j hij hj_lt
        by_cases h_eq : j = i
        · rw [h_eq]
          simp [getElem!_eq_getElem arr i hi, hp]
        · exact h_all j (by omega) hj_lt
      · right
        have h_forall : ∀ j, i ≤ j → j < k → p (arr[j]!) = false := by
          intro j hij hj_lt
          by_cases h_eq : j = i
          · rw [h_eq]
            simp [getElem!_eq_getElem arr i hi, hp]
          · exact hk_all j (by omega) hj_lt
        exact ⟨k, by omega, hk_sz, hk_eq, hk_pal, h_forall⟩
  · rw [dif_neg hi]
    left
    have h_forall : ∀ j, i ≤ j → j < arr.size → p (arr[j]!) = false := by
      intro j hij hj_lt; omega
    exact And.intro rfl h_forall
termination_by arr.size - i
decreasing_by
  omega

/-! ### Linear value search from an index (returning `Int` with `-1` sentinel) -/

/-- Search for `target` in `arr` starting from index `i`, returning the index as an `Int`.
Returns `-1` if `target` is not found at or after index `i`.
This is a linear search returning `Int` with `-1` as sentinel; for an idiomatic
`Option`-based index search, see `findFirstIdx`. -/
def linearSearchFrom {α : Type} [DecidableEq α] (arr : Array α) (target : α) (i : Nat) : Int :=
  if h : i < arr.size then
    if arr[i] = target then
      (i : Int)
    else
      linearSearchFrom arr target (i + 1)
  else
    -1
termination_by arr.size - i
decreasing_by
  simp_wf
  omega

/-- Specification for `linearSearchFrom`:
either it returns `-1` (target not found from `i` onward),
or it returns the **first** index `k ≥ i` where `arr[k]! = target`.

In the success case, `∀ j, i ≤ j → j < k → arr[j]! ≠ target` guarantees
that `k` is indeed the first occurrence at or after `i`. -/
lemma linearSearchFrom_spec {α : Type} [DecidableEq α] [Inhabited α]
    (arr : Array α) (target : α) (i : Nat) :
    (linearSearchFrom arr target i = (-1 : Int) ∧ ∀ j, i ≤ j → j < arr.size → arr[j]! ≠ target) ∨
    (∃ (k : Nat), i ≤ k ∧ k < arr.size ∧ arr[k]! = target ∧
      linearSearchFrom arr target i = (k : Int) ∧
      ∀ j, i ≤ j → j < k → arr[j]! ≠ target) := by
  induction' hk : arr.size - i using Nat.strong_induction_on with d ih generalizing i
  unfold linearSearchFrom
  split
  · rename_i hsz
    split
    · rename_i heq
      right
      refine ⟨i, le_refl i, hsz, ?_, rfl, ?_⟩
      · rw [getElem!_eq_getElem arr i hsz, heq]
      · intro j hi_j hj_i; omega
    · rename_i hne
      have hmeasure : arr.size - (i + 1) < d := by omega
      have ih_call := ih (arr.size - (i + 1)) hmeasure (i + 1) rfl
      rcases ih_call with (⟨h_res, h_all⟩ | ⟨k, h_ik, h_klt, h_keq, h_res, h_none⟩)
      · left
        refine ⟨by simpa [hsz, hne] using h_res, ?_⟩
        intro j hj_le hj_size
        by_cases h_eq_ij : i = j
        · subst h_eq_ij
          have h_get_eq : arr[i]! = arr[i] := getElem!_eq_getElem arr i hsz
          rw [h_get_eq]
          exact hne
        · have h_le : i + 1 ≤ j := by omega
          exact h_all j h_le hj_size
      · right
        refine ⟨k, by omega, h_klt, h_keq, by simpa [hsz, hne] using h_res, ?_⟩
        intro j hj_le hj_k
        by_cases h_eq_ij : i = j
        · subst h_eq_ij
          have h_get_eq : arr[i]! = arr[i] := getElem!_eq_getElem arr i hsz
          rw [h_get_eq]
          exact hne
        · have h_le : i + 1 ≤ j := by omega
          exact h_none j h_le hj_k
  · rename_i h_not_sz
    left
    refine ⟨rfl, ?_⟩
    intro j hj_le hj_size
    omega

/-- Specialization of `linearSearchFrom_spec` at starting index 0, with simplified
hypotheses (dropping the `0 ≤ j` / `0 ≤ k` conditions that are always true). -/
lemma linearSearchFrom_zero_spec {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (target : α) :
    (linearSearchFrom arr target 0 = (-1 : Int) ∧ ∀ j, j < arr.size → arr[j]! ≠ target) ∨
    (∃ (k : Nat), k < arr.size ∧ arr[k]! = target ∧
      linearSearchFrom arr target 0 = (k : Int) ∧
      ∀ j, j < k → arr[j]! ≠ target) := by
  have h := linearSearchFrom_spec arr target 0
  rcases h with (⟨h_res, h_all⟩ | ⟨k, h_0k, h_klt, h_keq, h_res, h_none⟩)
  · left; exact ⟨h_res, λ j hj => h_all j (Nat.zero_le _) hj⟩
  · right; exact ⟨k, h_klt, h_keq, h_res, λ j hj => h_none j (Nat.zero_le _) hj⟩


end Array

namespace Array


/-! ### Strictly increasing chain scanner -/

/-- Scan `arr` forward from index `i` with initial comparator `prev`,
returning the first index `r ≥ i` where the consecutive strict-comparison chain
`prev < arr[i]! < arr[i+1]! < ... < arr[r-1]!` breaks, or `r = arr.size` if the
entire suffix is strictly increasing relative to `prev`.

Formally, the returned `r` satisfies `i ≤ r ≤ arr.size`, and:
- For all `k` with `i ≤ k < r`, the chain of consecutive `(· < ·)` comparisons holds.
- If `r < arr.size`, then `¬ (arr[r-1]! < arr[r]!)` (or `¬ (prev < arr[r]!)` when `r = i`).

This is useful for finding the length of a strictly increasing prefix, e.g. in
"remove duplicates from sorted array"-style problems. -/
def strictIncChainEnd {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α] (arr : Array α) (i : Nat) (prev : α) : Nat :=
  if h : i < arr.size then
    let cur := arr[i]!
    if prev < cur then
      strictIncChainEnd arr (i+1) cur
    else
      i
  else
    arr.size
termination_by arr.size - i


/-! ### Sorted array lemmas -/

/-- If an `Array Nat` is sorted strictly (i.e., `i < j` implies `a[i]! ≤ a[j]!`), then the
same property holds for `i ≤ j`. This extends the sortedness hypothesis from strict `i < j`
to non-strict `i ≤ j`. -/
lemma sorted_nonstrict (a : Array Nat) (hsorted : ∀ i j, i < j → i < a.size → j < a.size → a[i]! ≤ a[j]!)
    (i j : Nat) (hij : i ≤ j) (hi : i < a.size) (hj : j < a.size) : a[i]! ≤ a[j]! := by
  rcases lt_or_eq_of_le hij with (hlt | heq)
  · exact hsorted i j hlt hi hj
  · subst heq
    rfl

/-- If an array is strictly sorted (i.e., `i < j` implies `a[i]! < a[j]!`), then
`i ≤ j` implies `a[i]! ≤ a[j]!`. This derives the non-strict `≤` property
from a strict-`<` sortedness hypothesis.

Generalized from `Nat` to any `Preorder α` with an `Inhabited` instance.

Contrast with `sorted_nonstrict` which takes a `≤`-sorted hypothesis and is `Nat`-specific. -/
lemma sorted_le_of_le {α : Type} [Preorder α] [Inhabited α] {nums : Array α} {i j : Nat}
    (h_sorted : ∀ i j : Nat, i < j → i < nums.size → j < nums.size → nums[i]! < nums[j]!)
    (hij : i ≤ j) (hi : i < nums.size) (hj : j < nums.size) : nums[i]! ≤ nums[j]! := by
  rcases Nat.eq_or_lt_of_le hij with (rfl | hlt)
  · rfl
  · exact le_of_lt (h_sorted i j hlt hi hj)

/-- In a strictly sorted array, if `target < nums[mid]!` and `mid ≤ i`, then
`target < nums[i]!`. This is a transitivity lemma used in binary search correctness proofs:
once we know the target is less than the middle element, it must also be less than
any element to the right of the middle. -/
lemma target_lt_of_sorted_and_mid_le {α : Type} [Preorder α] [Inhabited α] {nums : Array α} {target : α} {mid i : Nat}
    (h_sorted : ∀ i j : Nat, i < j → i < nums.size → j < nums.size → nums[i]! < nums[j]!)
    (h_target_lt_mid : target < nums[mid]!) (h_mid_le_i : mid ≤ i) (hmid_sz : mid < nums.size)
    (hi_sz : i < nums.size) : target < nums[i]! := by
  have hle : nums[mid]! ≤ nums[i]! := sorted_le_of_le h_sorted h_mid_le_i hmid_sz hi_sz
  exact lt_of_lt_of_le h_target_lt_mid hle

/-- In a sorted array, if all elements before index `i` are `≤ target`, and
`arr[j]! > target`, then `arr[i]! ≤ arr[j]!`. This follows from sortedness:
either `j < i` (impossible by `hfirst`) or `i ≤ j` (sortedness applies).

This lemma is used to prove that `firstGreaterIdx` returns the *minimal* index
whose value exceeds `target`. -/
lemma le_of_sorted_and_forall_before_le {α : Type} [LinearOrder α] [Inhabited α] (arr : Array α) (target : α) (i j : Nat)
    (hsorted : ∀ p q, p < arr.size → q < arr.size → p < q → arr[p]! ≤ arr[q]!)
    (hi : i < arr.size) (hj : j < arr.size)
    (hfirst : ∀ k, k < i → arr[k]! ≤ target)
    (hj_gt : arr[j]! > target) :
    arr[i]! ≤ arr[j]! := by
  by_cases hji : j < i
  · have hle := hfirst j hji
    exact absurd hj_gt (not_lt.mpr hle)
  · have hij : i ≤ j := by omega
    rcases hij.eq_or_lt with (heq | hlt)
    · subst heq; exact le_refl _
    · exact hsorted i j hi hj hlt


/-! ### Binary search on sorted arrays -/

/-- Recursive binary search for `target` in the subarray `nums[lo..<hi]`.
Returns the index as an `Int` (using `Int.ofNat`) if found, or `-1` if not found.
The caller must ensure the array is strictly sorted for correctness of the result.

Generalized to any `LinearOrder α` with an `Inhabited` instance. -/
def binarySearchAux {α : Type} [LinearOrder α] [Inhabited α] (nums : Array α) (target : α) (lo hi : Nat) : Int :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if hmid : mid < nums.size then
      let val := nums[mid]!
      if val = target then
        Int.ofNat mid
      else if val < target then
        binarySearchAux nums target (mid + 1) hi
      else
        binarySearchAux nums target lo mid
    else
      -1
  else
    -1
termination_by hi - lo
decreasing_by
  all_goals omega

/-- Binary search for `target` in the entire array `nums[0..<nums.size]`.
Returns the index as an `Int` (using `Int.ofNat`) if found, or `-1` if not found.
The caller must ensure the array is strictly sorted for correctness of the result.

This is a convenience wrapper around `binarySearchAux`. -/
def binarySearch {α : Type} [LinearOrder α] [Inhabited α] (nums : Array α) (target : α) : Int :=
  binarySearchAux nums target 0 nums.size


end Array


namespace Array

/-! ### "All from" — check that a predicate holds on a suffix -/

/--
`allFrom arr pred start` returns `true` iff `pred` holds for every element of `arr`
from index `start` to `arr.size - 1`.
-/
def allFrom (arr : Array α) [Inhabited α] (pred : α → Bool) (start : Nat) : Bool :=
  if h : start < arr.size then
    pred (arr[start]!) && allFrom arr pred (start + 1)
  else
    true
termination_by arr.size - start

/-- Correctness lemma for `allFrom`: `allFrom arr pred k` returns true iff `pred` holds
for every element of `arr` from index `k` to `arr.size - 1`. -/
theorem allFrom_spec (arr : Array α) [Inhabited α] (pred : α → Bool) (k : Nat) :
    allFrom arr pred k = true ↔ (∀ i, k ≤ i → i < arr.size → pred (arr[i]!) = true) := by
  rw [allFrom]
  split
  · rename_i hk
    simp [Bool.and_eq_true, decide_eq_true_iff]
    constructor
    · intro ⟨hcur, hrest⟩
      intro i hki hi
      rcases Nat.eq_or_lt_of_le hki with (rfl | hlt)
      · exact hcur
      · have hrest' := (allFrom_spec arr pred (k + 1)).mp hrest
        exact hrest' i (Nat.succ_le_of_lt hlt) hi
    · intro h
      constructor
      · exact h k (Nat.le_refl k) hk
      · apply (allFrom_spec arr pred (k + 1)).mpr
        intro i hki hi
        apply h i (Nat.le_trans (Nat.le_succ k) hki) hi
  · rename_i hk
    constructor
    · intro _h
      intro i hki hi
      exfalso
      exact hk (Nat.lt_of_le_of_lt hki hi)
    · intro _h
      rfl
termination_by arr.size - k

end Array
