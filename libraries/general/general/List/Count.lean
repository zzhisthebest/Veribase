import Mathlib
import general.List.Sequences
import general.List.ExtremumSelection
import general.List.Membership
import general.List.Sort
import general.List.Aggregation
import general.List.Slicing

namespace List

/-! ### `countWithIndex` — count elements where an indexed predicate holds -/

/-- Auxiliary: count elements starting at index `i` for `countWithIndex`. -/
private def countWithIndexAux {α : Type} (p : α → Nat → Bool) : List α → Nat → Nat
  | [], _ => 0
  | x :: rest, i => (if p x i then 1 else 0) + countWithIndexAux p rest (i+1)

/-- Count elements in a list satisfying an indexed predicate `p : α → Nat → Bool`.
The predicate receives both the element and its zero-based index.
For example, `countWithIndex [a, b, c] (fun x i => x = i)` counts how many elements
equal their position. -/
def countWithIndex {α : Type} (xs : List α) (p : α → Nat → Bool) : Nat :=
  countWithIndexAux p xs 0


lemma countWithIndex_nil {α : Type} (p : α → Nat → Bool) : countWithIndex [] p = 0 := rfl

private lemma countWithIndexAux_shift {α : Type} (p : α → Nat → Bool) (xs : List α) (k : Nat) :
    countWithIndexAux p xs (k + 1) = countWithIndexAux (fun y i => p y (i + 1)) xs k := by
  induction xs generalizing k with
  | nil => simp [countWithIndexAux]
  | cons y ys ih =>
    simp [countWithIndexAux, ih, Nat.succ_eq_add_one, add_assoc]

lemma countWithIndex_cons {α : Type} (x : α) (xs : List α) (p : α → Nat → Bool) :
    countWithIndex (x :: xs) p = (if p x 0 then 1 else 0) + countWithIndex xs (fun y i => p y (i + 1)) := by
  simp [countWithIndex, countWithIndexAux, countWithIndexAux_shift]

/-! ### `countIfAux` — tail-recursive count by predicate with accumulator -/

/-- Tail-recursive count of elements in `lst` that satisfy predicate `p`,
starting from `acc`. Equivalent to `acc + (lst.filter p).length` but tail-recursive. -/
def countIfAux {α : Type} (p : α → Bool) (lst : List α) (acc : Nat) : Nat :=
  match lst with
  | []      => acc
  | x :: xs => countIfAux p xs (if p x then acc + 1 else acc)

/-- If `p x` holds, `countIfAux` increments by one. -/
theorem countIfAux_cons_of_pos {α : Type} {p : α → Bool} {x : α} {xs : List α} {acc : Nat}
    (h : p x) : countIfAux p (x :: xs) acc = countIfAux p xs (acc + 1) := by
  simp [countIfAux, h]

/-- The accumulator-based `countIfAux` equals `acc` plus the length of the filtered list. -/
theorem countIfAux_eq_add_filter_length {α : Type} (p : α → Bool) (lst : List α) (acc : Nat) :
    countIfAux p lst acc = acc + (lst.filter p).length := by
  induction lst generalizing acc with
  | nil => simp [countIfAux]
  | cons x xs ih =>
    by_cases h : p x
    · simp [countIfAux, h, ih, List.filter]
      omega
    · simp [countIfAux, h, ih, List.filter]

/-- Starting from `0`, `countIfAux` just returns the number of matching elements. -/
theorem countIfAux_zero_eq_filter_length {α : Type} (p : α → Bool) (lst : List α) :
    countIfAux p lst 0 = (lst.filter p).length := by
  simp [countIfAux_eq_add_filter_length]

/-! ### `countWhile` — count consecutive elements satisfying a predicate from the start

`countWhile p l` returns the length of the longest prefix of `l` where every element
satisfies `p`. Unlike `countP` (which counts *all* matching elements), `countWhile`
stops at the first element that does *not* satisfy `p`.

Example: `countWhile (· ≤ 3) [1, 2, 3, 4, 5] = 3` (stops at `4`). -/

/-- Count the number of elements from the start of the list that satisfy predicate `p`.
Stops counting when the first element not satisfying `p` is encountered. -/
def countWhile {α : Type} (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | x :: xs => if p x then 1 + countWhile p xs else 0

/-- The number of consecutive elements satisfying `p` is bounded by the list length. -/

lemma countWhile_nil {α : Type} (p : α → Prop) [DecidablePred p] : countWhile p ([] : List α) = 0 := rfl


lemma countWhile_cons_of_pos {α : Type} (p : α → Prop) [DecidablePred p] {x : α} {xs : List α}
    (h : p x) : countWhile p (x :: xs) = 1 + countWhile p xs := by
  simp [countWhile, h]


lemma countWhile_cons_of_neg {α : Type} (p : α → Prop) [DecidablePred p] {x : α} {xs : List α}
    (h : ¬ p x) : countWhile p (x :: xs) = 0 := by
  simp [countWhile, h]

lemma countWhile_le_length {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) :
    l.countWhile p ≤ l.length := by
  induction l with
  | nil => simp [countWhile]
  | cons x xs ih =>
    by_cases h : p x <;> simp [countWhile, h] <;> omega

/-- Every element whose index is strictly less than `countWhile p l` satisfies `p`
and is a valid index in `l`. In other words, all elements in the `countWhile`-prefix
satisfy the predicate. -/
lemma countWhile_getElem?_satisfies {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) (i : Nat)
    (hi : i < l.countWhile p) : ∃ a : α, l[i]? = some a ∧ p a := by
  induction l generalizing i with
  | nil => simp [countWhile] at hi
  | cons x xs ih =>
    by_cases h : p x
    · cases i with
      | zero => exact ⟨x, rfl, h⟩
      | succ i =>
        have hi' : i < xs.countWhile p := by simp [countWhile, h] at hi; omega
        simpa using ih i hi'
    · simp [countWhile, h] at hi

/-- In a sorted list `l`, if we take the prefix of elements ≤ `a` (via `countWhile`),
then any element at or beyond that prefix (but within the list) must be strictly
greater than `a`. This is the key property linking `countWhile` to sorted list
insertion positions. -/
lemma sorted_countWhile_not {α : Type} [LinearOrder α] (l : List α) (a : α)
    (h_sorted : List.Sorted (· ≤ ·) l) (i : Nat)
    (hge : l.countWhile (λ x => x ≤ a) ≤ i) (hlt : i < l.length) :
    ∃ v : α, l[i]? = some v ∧ a < v := by
  induction l generalizing i with
  | nil => simp at hlt
  | cons x xs ih =>
      rcases List.sorted_cons.mp h_sorted with ⟨h_all, h_sorted_xs⟩
      simp [countWhile] at hge
      by_cases hx : x ≤ a
      · simp [hx] at hge
        cases i with
        | zero => omega
        | succ i' =>
            have hge' : xs.countWhile (λ x => x ≤ a) ≤ i' := by omega
            have hlt' : i' < xs.length := by
              simp at hlt; omega
            rcases ih h_sorted_xs i' hge' hlt' with ⟨v, hv, hv_gt⟩
            exact ⟨v, by simp [hv], hv_gt⟩
      · simp [hx] at hge
        have ha_lt_x : a < x := lt_of_not_ge hx
        cases i with
        | zero =>
            exact ⟨x, by simp, ha_lt_x⟩
        | succ i' =>
            have hlt' : i' < xs.length := by
              simp at hlt; omega
            have hsome : xs[i']? ≠ none := by
              intro heq
              have hlen := (List.getElem?_eq_none_iff.mp heq)
              omega
            rcases Option.ne_none_iff_exists'.mp hsome with ⟨v, hv⟩
            have hv_mem : v ∈ xs := List.mem_of_getElem? hv
            have hx_le_v : x ≤ v := h_all v hv_mem
            have ha_lt_v : a < v := lt_of_lt_of_le ha_lt_x hx_le_v
            exact ⟨v, by simp [hv], ha_lt_v⟩

/-! ### `countOcc` — count occurrences of a specific element -/

/-- Count occurrences of a specific element `r` in a list `l`.
Equivalent to `countOccurrences` (defined in `general.List`). -/
def countOcc {α : Type} [DecidableEq α] (r : α) (l : List α) : Nat :=
  (l.filter fun x => x = r).length


lemma countOcc_nil {α : Type} [DecidableEq α] (r : α) : countOcc r [] = 0 := rfl

lemma countOcc_cons {α : Type} [DecidableEq α] (r x : α) (xs : List α) :
    countOcc r (x :: xs) = (if x = r then 1 else 0) + countOcc r xs := by
  unfold countOcc
  simp only [List.filter_cons, List.length_cons]
  by_cases h : x = r
  · simp [h]; omega
  · simp [h]


lemma countOcc_cons_eq {α : Type} [DecidableEq α] (a : α) (l : List α) :
    countOcc a (a :: l) = countOcc a l + 1 := by
  unfold countOcc; simp

lemma countOcc_cons_ne {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) (l : List α) :
    countOcc a (b :: l) = countOcc a l := by
  unfold countOcc
  have h' : b ≠ a := Ne.symm h
  simp [h']

/-- Count occurrences of a specific element `a` in a list `l`. -/
def countOccurrences [DecidableEq α] (a : α) (l : List α) : Nat :=
  (l.filter (fun x => decide (x = a))).length

lemma countOcc_eq_countOccurrences {α : Type} [DecidableEq α] (r : α) (l : List α) :
    countOcc r l = countOccurrences r l := rfl

/-! ### Theorems about `countOcc` -/

/-- If `r` is not in `l`, then `countOcc r l = 0`. -/
lemma countOcc_eq_zero_of_not_mem {α : Type} [DecidableEq α] {r : α} {l : List α} (h : r ∉ l) :
    countOcc r l = 0 := by
  unfold countOcc
  have h_filter : l.filter (fun x => x = r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hx_ne_r : x ≠ r := by
      intro h_eq
      have : r ∈ l := by rw [← h_eq]; exact hx
      exact h this
    simpa using hx_ne_r
  simp [h_filter]

/-- `countOcc r l = 0` iff `r` does not appear in `l`. -/
lemma countOcc_eq_zero_iff_not_mem {α : Type} [DecidableEq α] {r : α} {l : List α} :
    countOcc r l = 0 ↔ r ∉ l := by
  constructor
  · intro hzero hmem
    have hpos : countOcc r l > 0 := by
      unfold countOcc
      have hmem_filter : r ∈ l.filter (fun x => decide (x = r)) := by
        apply List.mem_filter.mpr
        exact ⟨hmem, by simp⟩
      exact List.length_pos_of_mem hmem_filter
    omega
  · exact countOcc_eq_zero_of_not_mem

/-- If `countOcc r l > 0`, then `r ∈ l`. -/
lemma countOcc_pos_imp_mem {α : Type} [DecidableEq α] {r : α} {l : List α} (h : countOcc r l > 0) :
    r ∈ l := by
  by_contra h_not
  have hzero : countOcc r l = 0 := countOcc_eq_zero_of_not_mem h_not
  omega

/-- If `List.count a l > 1`, then `a ∈ l`.
This is a convenient shortcut combining `List.count_pos_iff` with `omega`. -/
lemma count_gt_one_imp_mem [BEq α] [LawfulBEq α] (l : List α) (a : α) (h : List.count a l > 1) :
    a ∈ l :=
  List.count_pos_iff.mp (by omega : 0 < List.count a l)

/-- `0 < countOcc r l` iff `r` appears in `l`. -/
lemma countOcc_pos_iff_mem {α : Type} [DecidableEq α] {r : α} {l : List α} :
    0 < countOcc r l ↔ r ∈ l := by
  constructor
  · exact countOcc_pos_imp_mem
  · intro hmem
    unfold countOcc
    have hm : r ∈ l.filter (fun x => x = r) :=
      List.mem_filter.mpr ⟨hmem, by simp⟩
    exact List.length_pos_of_mem hm

/-- Counting occurrences distributes over list concatenation:
`countOcc r (l1 ++ l2) = countOcc r l1 + countOcc r l2`. -/
lemma countOcc_append {α : Type} [DecidableEq α] (r : α) (l1 l2 : List α) :
    countOcc r (l1 ++ l2) = countOcc r l1 + countOcc r l2 := by
  simp [countOcc, List.filter_append, List.length_append]

/-- If the total count of `a` across two concatenated lists is exactly 1,
then `a` appears in exactly one of them (count 1) and not in the other (count 0).
Useful for reasoning about exclusive occurrences in split lists. -/
lemma countOcc_sum_eq_one_cases {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α)
    (h : countOcc a (l₁ ++ l₂) = 1) :
    (countOcc a l₁ = 1 ∧ countOcc a l₂ = 0) ∨
    (countOcc a l₁ = 0 ∧ countOcc a l₂ = 1) := by
  rw [countOcc_append] at h
  omega

/-- Counting occurrences of `r` in `List.replicate n a`:
each of the `n` copies is `a`, so the result is `n` if `a = r`, else `0`. -/
lemma countOcc_replicate {α : Type} [DecidableEq α] (r a : α) (n : Nat) :
    countOcc r (List.replicate n a) = if a = r then n else 0 := by
  induction n with
  | zero => simp [countOcc]
  | succ n ih =>
    simp [List.replicate_succ, countOcc, List.filter_cons, ih]
    by_cases h : a = r
    · simp [h]
    · simp [h]

/-- For `n > 0`, checking with `any` whether some element has count ≥ n
is equivalent to the existential statement. This is the core equivalence
behind `hasCountGE` in counting problems. -/
lemma any_countOcc_ge_iff {α : Type} [DecidableEq α] {n : Nat} {l : List α} (hn : n > 0) :
    (l.any (fun r => countOcc r l ≥ n)) = true ↔ ∃ r, countOcc r l ≥ n := by
  constructor
  · intro h
    rcases (List.any_eq_true (p := fun r => countOcc r l ≥ n)).mp h with ⟨r, hr, hcount⟩
    have hcount' : countOcc r l ≥ n := by
      simpa using hcount
    exact ⟨r, hcount'⟩
  · intro ⟨r, hcount⟩
    have hr_mem : r ∈ l := countOcc_pos_imp_mem (by omega)
    apply (List.any_eq_true (p := fun r' => countOcc r' l ≥ n)).mpr
    exact ⟨r, hr_mem, by simpa using hcount⟩

/-! ### `elementsWithCount` and `singles` — filter elements by frequency -/

/-- Returns the deduplicated sublist of elements that appear exactly `n` times in `lst`.
Each element is included at most once, even if it appears `n > 0` times in the original list.
Use `lst.filter (fun x => lst.count x = n)` if you need each occurrence preserved. -/
def elementsWithCount {α : Type} [DecidableEq α] (lst : List α) (n : Nat) : List α :=
  (lst.dedup).filter (fun x => lst.count x = n)

/-- `elementsWithCount` always returns a `Nodup` list. -/
lemma nodup_elementsWithCount {α : Type} [DecidableEq α] (lst : List α) (n : Nat) :
    (elementsWithCount lst n).Nodup := by
  unfold elementsWithCount
  exact List.Nodup.filter _ (List.nodup_dedup lst)

/-- Membership in `elementsWithCount lst n` is equivalent to being in `lst` and having count `n`. -/
lemma mem_elementsWithCount_iff {α : Type} [DecidableEq α] {lst : List α} {x : α} {n : Nat} :
    x ∈ elementsWithCount lst n ↔ (x ∈ lst ∧ lst.count x = n) := by
  unfold elementsWithCount
  simp [List.mem_filter, List.mem_dedup, decide_eq_true_iff]

/-- If an element is in a list and has occurrence count exactly 1, then it belongs to
the deduplicated sublist of elements whose count is 1. This is a frequently used
lemma for extracting "unique" elements from a list, e.g., words that appear exactly once. -/
lemma mem_dedup_filter_of_mem_and_countOcc_one {α : Type} [DecidableEq α] {a : α} {l : List α}
    (hmem : a ∈ l) (hcnt : countOcc a l = 1) :
    a ∈ (l.filter (fun x => countOcc x l = 1)).dedup := by
  have hmem_filter : a ∈ l.filter (fun x => countOcc x l = 1) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simpa using hcnt⟩
  rw [List.mem_dedup]
  exact hmem_filter

/-- Alias: sublist of elements that appear exactly once in `lst`. -/
def singles {α : Type} [DecidableEq α] (lst : List α) : List α :=
  lst.elementsWithCount 1

/-- An element belongs to `singles lst` iff it appears exactly once in `lst`. -/
lemma mem_singles_iff {α : Type} [DecidableEq α] (lst : List α) (x : α) :
    x ∈ lst.singles ↔ lst.count x = 1 := by
  unfold List.singles List.elementsWithCount
  simp only [List.mem_filter, List.mem_dedup, decide_eq_true_iff]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h
    have hmem : x ∈ lst := by
      rw [← List.count_pos_iff, h]; norm_num
    exact ⟨hmem, h⟩

/-- If an element appears exactly once in `lst`, then its count in `singles lst` is also 1. -/
lemma count_singles_of_count_one {α : Type} [DecidableEq α] (lst : List α) (x : α)
    (h : lst.count x = 1) : List.count x (lst.singles) = 1 := by
  have hsingles_mem : x ∈ lst.singles := (mem_singles_iff lst x).mpr h
  have hsingles_nodup : lst.singles.Nodup := by
    unfold List.singles; exact nodup_elementsWithCount lst 1
  exact List.count_eq_one_of_mem hsingles_nodup hsingles_mem

/-! ### Partition: `filterNe` length + count of `a` = total length -/

/-- For any list and element `a`, the length of `filter (≠ a)` plus
the count of `a` equals the total length. This decomposes the list into
"elements not equal to `a`" and "count of `a`". -/
lemma length_filter_ne_add_count_eq_length {α : Type u} [DecidableEq α] (l : List α) (a : α) :
    (l.filter (fun x => x ≠ a)).length + l.count a = l.length := by
  induction' l with h t ih
  · rfl
  · rw [List.filter_cons, List.count_cons, List.length_cons]
    by_cases h_eq : h = a
    · rw [h_eq]
      have hdec : decide ((a : α) ≠ a) = false := by simp
      have hbeq : (a == a) = true := by simp
      rw [hdec, hbeq]
      calc
        (t.filter (fun x => x ≠ a)).length + (t.count a + 1) =
            ((t.filter (fun x => x ≠ a)).length + t.count a) + 1 := by omega
        _ = t.length + 1 := by rw [ih]
    · have hdec : decide (h ≠ a) = true := decide_eq_true h_eq
      have hbeq : (h == a) = false := by simp [h_eq]
      rw [hdec, hbeq]
      simp only [List.length_cons, add_zero]
      calc
        (t.filter (fun x => x ≠ a)).length + 1 + t.count a =
            ((t.filter (fun x => x ≠ a)).length + t.count a) + 1 := by omega
        _ = t.length + 1 := by rw [ih]

/-- Appending `filter (≠ a)` with `replicate (count a l) a` preserves the list length.
This is a direct consequence of `length_filter_ne_add_count_eq_length`. -/
lemma length_filter_append_replicate_eq_length {α : Type u} [DecidableEq α] (l : List α) (a : α) :
    ((l.filter (fun x => x ≠ a)) ++ List.replicate (l.count a) a).length = l.length := by
  rw [List.length_append, List.length_replicate]
  exact length_filter_ne_add_count_eq_length l a

/-! ### `countBitSet` — count how many elements in a list have a specific bit set -/

/-- Count how many natural numbers in `nums` have bit `i` set.
Useful for bit problems operating on lists of numbers, such as bitwise majority
or computing the result of a bitwise OR/AND across list elements. -/
def countBitSet (nums : List Nat) (i : Nat) : Nat :=
  (nums.filter (fun n => Nat.testBit n i)).length

/-! ### `countSwapsToRight` — minimum adjacent swaps to move all matching elements right

Given a predicate `p`, `countSwapsToRight p xs` computes the minimum number of
adjacent swaps needed to move all elements satisfying `p` to the right end of the
list, while preserving relative order within each group (p-satisfying and non-p-satisfying).
It does this by reversing the list and counting, for each p-satisfying element, the number
of non-p-satisfying elements that appear *after* it in the original list. -/

/--
Given a list `xs` and a predicate `p`, computes the sum over all
p-satisfying elements of the number of non-p-satisfying elements
that appear *after* them.  This equals the minimum number of adjacent
swaps required to move all p-satisfying elements to the right end
of the list while preserving relative order within each group.
-/
def countSwapsToRight (p : α → Bool) (xs : List α) : Nat :=
  let rec go (l : List α) (rightCount : Nat) (acc : Nat) : Nat :=
    match l with
    | [] => acc
    | x :: xs' =>
        if p x then go xs' rightCount (acc + rightCount)
        else go xs' (rightCount + 1) acc
  go (xs.reverse) 0 0

/--
`countSwapsToRight` on an empty list is zero.
-/

lemma countSwapsToRight_nil (p : α → Bool) : countSwapsToRight p [] = 0 :=
  rfl

/-! ### `allCountEqual` — every element in a list has the same count -/

/-- `allCountEqual l k` asserts that every element `c` appearing in `l`
occurs exactly `k` times in `l`. Equivalent to `∀ c ∈ l, List.count c l = k`. -/
def allCountEqual [BEq α] (l : List α) (k : Nat) : Prop :=
  ∀ c ∈ l, l.count c = k

/-- The empty list trivially satisfies `allCountEqual` for any `k`. -/

lemma allCountEqual_nil [BEq α] (k : Nat) : allCountEqual ([] : List α) k := by
  intro c hc
  exact absurd hc (List.not_mem_nil c)

/-! ### `countRunningGt` — count elements strictly greater than the running count -/

/-- Count elements in `l` that are strictly greater than the running count,
starting from threshold `d`. Each time an element exceeds the current threshold,
it is counted and the threshold increments by 1.

This implements the core algorithm of LeetCode 2960 "Count Tested Devices":
iterating through a list with a running threshold, count how many elements
exceed the number of already-counted preceding elements. -/
def countRunningGt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, d => if x > d then 1 + countRunningGt xs (d + 1) else countRunningGt xs d


theorem countRunningGt_nil (d : Nat) : countRunningGt [] d = 0 := rfl

theorem countRunningGt_cons (x d : Nat) (xs : List Nat) :
    countRunningGt (x :: xs) d = if x > d then 1 + countRunningGt xs (d + 1) else countRunningGt xs d :=
  rfl

theorem countRunningGt_cons_of_gt {x d : Nat} {xs : List Nat} (h : x > d) :
    countRunningGt (x :: xs) d = 1 + countRunningGt xs (d + 1) := by
  simp [countRunningGt_cons, h]

theorem countRunningGt_cons_of_le {x d : Nat} {xs : List Nat} (h : x ≤ d) :
    countRunningGt (x :: xs) d = countRunningGt xs d := by
  have hnot : ¬ x > d := Nat.not_lt.mpr h
  simp [countRunningGt_cons, hnot]

/-! ### `frequencies` — list of frequencies of distinct elements -/

/-- For a list, compute the list of frequencies of each distinct element,
in the order given by `eraseDup`. Returns a `List Nat` where the i-th element
is the count of the i-th distinct element in `l`.

Example: `frequencies [a, b, a, c, b, a] = [3, 2, 1]` (a→3, b→2, c→1). -/
def frequencies {α : Type} [DecidableEq α] (l : List α) : List Nat :=
  (l.eraseDup).map (fun x => l.count x)

/-! ### `maxFreq` — maximum frequency of any element in a list -/

/-- Auxiliary: compute the maximum of `orig.count v` for `v ∈ lst`. -/
def maxFreqAux {α : Type} [BEq α] (orig : List α) : List α → Nat
  | [] => 0
  | v :: rest => Nat.max (orig.count v) (maxFreqAux orig rest)

/-- Maximum frequency of any element in `lst`. That is, `max_{v ∈ lst} List.count v lst`. -/
def maxFreq {α : Type} [BEq α] (lst : List α) : Nat :=
  maxFreqAux lst lst

/-- Count elements with maximum frequency in a list.
Each element `v` in `lst` contributes 1 to the result if `lst.count v = maxFreq lst`,
so `countMaxFreq lst` sums the multiplicity of all elements that achieve the maximum. -/
def countMaxFreq {α : Type} [BEq α] (lst : List α) : Nat :=
  lst.foldl (fun acc v => if lst.count v = maxFreq lst then acc + 1 else acc) 0

/-- For any element `v ∈ lst`, its count in `orig` is at most `maxFreqAux orig lst`. -/
lemma maxFreqAux_ge_count {α : Type} [BEq α] (orig : List α) : ∀ (lst : List α) (v : α),
    v ∈ lst → orig.count v ≤ maxFreqAux orig lst := by
  intro lst v h
  induction lst with
  | nil => exact absurd h (List.not_mem_nil v)
  | cons x xs ih =>
    rw [maxFreqAux]
    rcases List.mem_cons.mp h with (rfl | hxs)
    · apply Nat.le_max_left
    · have hx := ih hxs
      apply le_trans hx (Nat.le_max_right _ _)

/-- For a nonempty `lst`, there exists `v ∈ lst` whose count in `orig` equals `maxFreqAux orig lst`. -/
lemma maxFreqAux_achieved {α : Type} [BEq α] (orig : List α) : ∀ (lst : List α),
    lst ≠ [] → ∃ v, v ∈ lst ∧ orig.count v = maxFreqAux orig lst := by
  intro lst hne
  induction lst with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rw [maxFreqAux]
    by_cases hxs : xs = []
    · subst hxs
      simp [maxFreqAux]
    · have h_ih := ih hxs
      rcases h_ih with ⟨v, hv, heq⟩
      by_cases hle : maxFreqAux orig xs ≤ orig.count x
      · exact ⟨x, List.mem_cons_self _ _, (Nat.max_eq_left hle).symm⟩
      · have hlt : orig.count x < maxFreqAux orig xs := Nat.lt_of_not_ge hle
        refine ⟨v, List.mem_cons_of_mem _ hv, ?_⟩
        rw [heq]
        apply (Nat.max_eq_right (Nat.le_of_lt hlt)).symm

/-- For any element `v ∈ lst`, its count in `lst` is at most `maxFreq lst`. -/
lemma maxFreq_ge_count {α : Type} [BEq α] {lst : List α} {v : α} (hv : v ∈ lst) :
    lst.count v ≤ maxFreq lst := by
  have := maxFreqAux_ge_count lst lst v hv
  simpa [maxFreq] using this

/-- For a nonempty `lst`, there exists `v ∈ lst` whose count equals `maxFreq lst`. -/
lemma maxFreq_achieved {α : Type} [BEq α] {lst : List α} (hne : lst ≠ []) :
    ∃ v, v ∈ lst ∧ lst.count v = maxFreq lst := by
  have := maxFreqAux_achieved lst lst hne
  simpa [maxFreq] using this

/-- `maxFreq` of the empty list is `0`. -/

lemma maxFreq_nil {α : Type} [BEq α] : maxFreq ([] : List α) = 0 :=
  rfl

/-! ### `modes` — elements achieving maximum frequency -/

/-- Return elements of `l` that achieve the maximum frequency (statistical modes).
Uses `maxFreq l` to find the maximum count among all elements, then returns each
distinct element whose count equals that maximum. If multiple elements share the
same maximum frequency, all of them are returned. -/
def modes {α : Type} [DecidableEq α] (l : List α) : List α :=
  let mf := maxFreq l
  l.dedup.filter (fun x => decide (l.count x = mf))

/-- Membership in `modes l` iff the element appears in `l` and its count equals `maxFreq l`. -/
lemma mem_modes_iff {α : Type} [DecidableEq α] {l : List α} {x : α} :
    x ∈ modes l ↔ x ∈ l ∧ l.count x = maxFreq l := by
  unfold modes
  simp [List.mem_filter, List.mem_dedup]

/-! ### `maxByFreq` — find the element with maximum frequency

`maxByFreq l` returns the element in `l` with the highest occurrence count,
with ties broken by selecting the larger element (according to `LinearOrder`).
Returns `none` iff `l` is empty.

Unlike `maxFreq` (which returns the maximum count as a `Nat`), `maxByFreq`
returns the element itself (as an `Option α`). -/

/-- Step function for selecting the element with maximum frequency.
Given a frequency function `freq : α → Nat`, current best candidate (or none),
and a new candidate `x`, returns the one with higher frequency.
Tie-breaking: if frequencies are equal, pick the larger element. -/
def maxByFreqStep [LinearOrder α] (freq : α → Nat) (acc : Option α) (x : α) : Option α :=
  match acc with
  | none => some x
  | some best =>
    let cntBest := freq best
    let cntX := freq x
    if cntX > cntBest ∨ (cntX = cntBest ∧ x > best) then some x else acc

/-- Return the most frequent element in `l`, tie-breaking by larger element.
Returns `none` iff `l` is empty. -/
def maxByFreq [LinearOrder α] (l : List α) : Option α :=
  l.dedup.foldl (maxByFreqStep (l.count ·)) none

/-- `maxByFreqStep` never returns `none`. -/
lemma maxByFreqStep_never_none [LinearOrder α] (freq : α → Nat) (acc : Option α) (x : α) :
    maxByFreqStep freq acc x ≠ none := by
  unfold maxByFreqStep
  cases acc with
  | none => simp
  | some best =>
    by_cases h : freq x > freq best ∨ (freq x = freq best ∧ x > best)
    · simp [h]
    · simp [h]

/-- `maxByFreqStep` result is either `some x` or the original accumulator. -/
lemma maxByFreqStep_eq_some_or [LinearOrder α] (freq : α → Nat) (acc : Option α) (x : α) :
    maxByFreqStep freq acc x = some x ∨ maxByFreqStep freq acc x = acc := by
  unfold maxByFreqStep
  cases acc with
  | none => simp
  | some best =>
    by_cases h : freq x > freq best ∨ (freq x = freq best ∧ x > best)
    · simp [h]
    · simp [h]

/-- `foldl` with a non-`none` initial accumulator and `maxByFreqStep` never returns `none`. -/
lemma foldl_maxByFreqStep_never_none [LinearOrder α] (freq : α → Nat) (candidates : List α) (init : Option α)
    (hinit : init ≠ none) : candidates.foldl (maxByFreqStep freq) init ≠ none := by
  induction' candidates with hd tl ih generalizing init
  · exact hinit
  · have hstep : maxByFreqStep freq init hd ≠ none := maxByFreqStep_never_none freq init hd
    apply ih
    exact hstep

/-- If `foldl` returns `some p`, then `p` is either `init` or in `candidates`. -/
lemma foldl_maxByFreqStep_mem [LinearOrder α] (freq : α → Nat) (candidates : List α) (init : α) (p : α)
    (h : candidates.foldl (maxByFreqStep freq) (some init) = some p) : p = init ∨ p ∈ candidates := by
  induction' candidates with hd tl ih generalizing init p
  · simp at h; subst h; left; rfl
  · simp [List.foldl] at h
    have hstep := maxByFreqStep_eq_some_or freq (some init) hd
    rcases hstep with (hstep | hstep)
    · rw [hstep] at h
      have ih_res := ih hd p h
      rcases ih_res with (rfl | hmem)
      · right; simp
      · right; simp [hmem]
    · rw [hstep] at h
      have ih_res := ih init p h
      rcases ih_res with (rfl | hmem)
      · left; rfl
      · right; simp [hmem]

/-- `maxByFreq` returns `none` iff the input list is empty. -/
lemma maxByFreq_eq_none_iff [LinearOrder α] (l : List α) : maxByFreq l = none ↔ l = [] := by
  constructor
  · intro h
    by_contra hne
    have hdedup_ne : l.dedup ≠ [] := dedup_ne_nil_of_ne_nil hne
    unfold maxByFreq at h
    have hfoldl_ne : l.dedup.foldl (maxByFreqStep (l.count ·)) none ≠ none := by
      cases hdedup' : l.dedup with
      | nil => contradiction
      | cons hd tl =>
        simp [hdedup']
        apply foldl_maxByFreqStep_never_none (l.count ·) tl (some hd)
        simp
    exact hfoldl_ne h
  · intro h
    subst h
    unfold maxByFreq
    simp

/-- If `maxByFreq` returns `some p`, then `p ∈ l`. -/
lemma maxByFreq_some_mem [LinearOrder α] (l : List α) (p : α) (h : maxByFreq l = some p) : p ∈ l := by
  unfold maxByFreq at h
  have hne : l ≠ [] := by
    intro hne
    subst hne
    simp at h
  have hdedup_ne : l.dedup ≠ [] := dedup_ne_nil_of_ne_nil hne
  cases hdedup : l.dedup with
  | nil => contradiction
  | cons hd tl =>
    rw [hdedup] at h
    simp at h
    have hmem := foldl_maxByFreqStep_mem (l.count ·) tl hd p h
    rcases hmem with (rfl | hmem)
    · apply (List.mem_dedup.mp ?_)
      rw [hdedup]
      simp
    · apply (List.mem_dedup.mp ?_)
      rw [hdedup]
      simp [hmem]

/-! ### `countOccInPrefix` — count occurrences in the first `n` elements -/

/-- Count occurrences of `a` in the first `n` elements of `xs`.
Equivalent to `countOcc a (xs.take n)`. -/
def countOccInPrefix {α : Type} [DecidableEq α] (xs : List α) (n : Nat) (a : α) : Nat :=
  countOcc a (xs.take n)


lemma countOccInPrefix_nil {α : Type} [DecidableEq α] (n : Nat) (a : α) :
    countOccInPrefix ([] : List α) n a = 0 := by
  simp [countOccInPrefix, countOcc]


lemma countOccInPrefix_zero {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    countOccInPrefix xs 0 a = 0 := by
  simp [countOccInPrefix, countOcc]

lemma countOccInPrefix_cons {α : Type} [DecidableEq α] (x : α) (xs : List α) (n : Nat) (a : α) :
    countOccInPrefix (x :: xs) (n + 1) a =
    (if x = a then 1 else 0) + countOccInPrefix xs n a := by
  simp [countOccInPrefix, countOcc_cons, show (x :: xs).take (n + 1) = x :: xs.take n by simp]

/-! ### `countElem` range-bound reduction to universal statement -/

/-- Count how many times `a` occurs in `xs`, using `foldl`. -/
def countElem {α : Type} [DecidableEq α] (a : α) (xs : List α) : Nat :=
  xs.foldl (λ acc x => if x = a then acc + 1 else acc) 0

/-- If `a` is not in `xs`, its `countElem` is zero. -/
lemma countElem_eq_zero_of_not_mem [DecidableEq α] {a : α} {xs : List α} (h : a ∉ xs) :
    countElem a xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hax : x ≠ a := by intro he; apply h; simp [he]
    have hxs : a ∉ xs := fun hm => h (List.mem_cons_of_mem x hm)
    simpa [countElem, hax] using ih hxs

/-- If all elements of `xs` lie in `[1, maxVal]`, and we know every value in that range
appears at most `k` times, then *every* natural number appears at most `k` times.
This is the key reduction from a finite check to a universal statement. -/
lemma countElem_le_from_range_check {xs : List Nat} {k maxVal : Nat}
    (h_range : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ maxVal)
    (h_fin : ∀ i, i < maxVal → countElem (i + 1) xs ≤ k) : ∀ x : Nat, countElem x xs ≤ k := by
  intro x
  by_cases h_in : 1 ≤ x ∧ x ≤ maxVal
  · rcases h_in with ⟨hlo, hhi⟩
    have hx' : x - 1 < maxVal := by omega
    have h_eq : (x - 1) + 1 = x := by omega
    have hc := h_fin (x - 1) hx'
    simpa [h_eq] using hc
  · have h_out : x < 1 ∨ x > maxVal := by
      rcases not_and_or.mp h_in with (hlt | hgt)
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have h_notmem : x ∉ xs := by
      intro hmem
      rcases h_range x hmem with ⟨hlo', hhi'⟩
      rcases h_out with (hlt | hgt)
      · linarith
      · linarith
    have hzero : countElem x xs = 0 := countElem_eq_zero_of_not_mem h_notmem
    rw [hzero]
    omega

/-! ### `countPairOccurrences` — count occurrences of a specific pair in a list of pairs -/

/-- Count occurrences of a specific pair `(a, b)` in a list of pairs.
`countPairOccurrences lst a b = |{p ∈ lst | p.1 = a ∧ p.2 = b}|`.

This is equivalent to `countOccurrences (a, b) lst`, since `α × β`
automatically carries a `DecidableEq` instance when both components do. -/
def countPairOccurrences [DecidableEq α] [DecidableEq β] (lst : List (α × β)) (a : α) (b : β) : Nat :=
  (lst.filter (fun p => p.1 = a ∧ p.2 = b)).length

/-- `countPairOccurrences` is equivalent to `countOccurrences` on the pair. -/
lemma countPairOccurrences_eq_countOccurrences [DecidableEq α] [DecidableEq β]
    (lst : List (α × β)) (a : α) (b : β) :
    countPairOccurrences lst a b = countOccurrences (a, b) lst := by
  unfold countPairOccurrences countOccurrences
  refine congrArg List.length ?_
  refine filter_congr ?_
  intro p _
  rcases p with ⟨x, y⟩
  simp

/-! ### `countDistinctFstBySnd` — count distinct first elements for a given second element -/

/-- Count the number of distinct first elements paired with a given second element
in a list of pairs.

For example, `countDistinctFstBySnd [(1, "a"), (2, "a"), (1, "b")] "a" = 2`
since first elements `1` and `2` are paired with `"a"`. -/
def countDistinctFstBySnd [DecidableEq α] [DecidableEq β] (pairs : List (α × β)) (key : β) : Nat :=
  ((pairs.filter (fun p => p.2 = key)).map Prod.fst).eraseDup.length

/-! ### `countByKey` — count entries with a given first component in a list of pairs -/

/-- Count the number of entries in a list of pairs whose first component equals `key`.
For example, `countByKey [(1, "a"), (2, "b"), (1, "c")] 1 = 2`.
Contrast with `countPairOccurrences` which matches both components. -/
def countByKey {α β : Type} [DecidableEq α] (rows : List (α × β)) (key : α) : Nat :=
  (rows.filter (fun r => r.1 = key)).length


theorem countByKey_nil {α β : Type} [DecidableEq α] (key : α) :
    countByKey ([] : List (α × β)) key = 0 := by
  simp [countByKey]

/-! ### `countMapEq` — count elements where `f x = y` -/

/-- Count the number of elements `x ∈ xs` such that `f x = y`.
This generalizes `countOcc` (which is the special case `f = id`).
For example, `countMapEq (fun x => x % 3) [1, 2, 3, 4, 5] 1 = 2` (since 1 and 4 ≡ 1 mod 3). -/
def countMapEq {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) (y : β) : Nat :=
  (xs.filter fun x => f x = y).length


lemma countMapEq_nil {α β : Type} [DecidableEq β] (f : α → β) (y : β) : countMapEq f [] y = 0 := rfl

lemma countMapEq_cons {α β : Type} [DecidableEq β] (f : α → β) (x : α) (xs : List α) (y : β) :
    countMapEq f (x :: xs) y = (if f x = y then 1 else 0) + countMapEq f xs y := by
  unfold countMapEq
  by_cases h : f x = y
  · simp [h, add_comm]
  · simp [h]

/-- `countMapEq` reduces to `countOcc` when `f = id`. -/
lemma countMapEq_eq_countOcc {α : Type} [DecidableEq α] (xs : List α) (y : α) :
    countMapEq id xs y = countOcc y xs := rfl

/-- Filtering a mapped list and the original list for a specific value `b` yields
equal lengths: `|{x ∈ xs.map f | x = b}| = |{x ∈ xs | f x = b}|`.
This is a key lemma relating filter-after-map to filter-before-map for equality predicates. -/
lemma length_filter_map_eq {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) (b : β) :
    List.length ((xs.map f).filter (fun x => x = b)) =
    List.length (xs.filter (fun x => f x = b)) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.filter_cons, List.length_cons]
    by_cases h : f hd = b
    · simp [h, ih]
    · simp [h, ih]

/-! ### `maxFreqSortedAux` and `maxFreqSorted` — O(n) max frequency on sorted lists

`maxFreqSortedAux` scans a list, tracking consecutive equal element runs.
For a sorted list, `maxFreqSorted` gives the same result as `maxFreq` but in O(n) time.

Contrast with `maxFreq` which uses `List.count` (O(n²) worst case) and works on unsorted lists. -/

/-- Auxiliary function: scan a list to find the maximum length of consecutive equal elements.
Parameters:
- `prev`: the previous element seen
- `cnt`: current run length
- `best`: maximum run length seen so far

For a sorted list, this gives `maxFreq`. -/
def maxFreqSortedAux [DecidableEq α] : List α → α → Nat → Nat → Nat
  | [], _, _, best => best
  | y :: ys, prev, cnt, best =>
    if y = prev then
      maxFreqSortedAux ys prev (cnt + 1) (max best (cnt + 1))
    else
      maxFreqSortedAux ys y 1 best

/-- Maximum frequency of any element in a sorted list.
O(n) time; assumes the list is sorted (equal elements are consecutive).
For unsorted lists, use `maxFreq`. -/
def maxFreqSorted [DecidableEq α] (lst : List α) : Nat :=
  match lst with
  | [] => 0
  | x :: xs => maxFreqSortedAux xs x 1 1

/-- `maxFreqSortedAux` is bounded by the maximum of `best` and `cnt + length`. -/
lemma maxFreqSortedAux_le_add [DecidableEq α] (lst : List α) (prev : α) (cnt best : Nat) (hcnt : 1 ≤ cnt) :
    maxFreqSortedAux lst prev cnt best ≤ max best (cnt + lst.length) := by
  induction lst generalizing prev cnt best with
  | nil =>
    simp [maxFreqSortedAux]
  | cons y ys ih =>
    unfold maxFreqSortedAux
    split
    · -- y = prev case
      have h_ih := ih prev (cnt + 1) (max best (cnt + 1)) (by omega)
      calc
        maxFreqSortedAux ys prev (cnt + 1) (max best (cnt + 1))
            ≤ max (max best (cnt + 1)) ((cnt + 1) + ys.length) := h_ih
        _ ≤ max (max best (cnt + 1 + ys.length)) ((cnt + 1) + ys.length) := by
          refine max_le_max ?_ (le_refl _)
          refine max_le_max (le_refl best) ?_
          omega
        _ = max best ((cnt + 1) + ys.length) :=
          max_eq_left (Nat.le_max_right best ((cnt + 1) + ys.length))
        _ = max best (cnt + 1 + ys.length) := by ring
        _ = max best (cnt + (y :: ys).length) := by
          simp [List.length_cons]; omega
    · -- y ≠ prev case
      have h_ih := ih y 1 best (by omega)
      calc
        maxFreqSortedAux ys y 1 best ≤ max best (1 + ys.length) := h_ih
        _ ≤ max best (cnt + (y :: ys).length) := by
          refine max_le_max (le_refl best) ?_
          simp [List.length_cons]
          omega

/-- Corollary: `maxFreqSortedAux xs x 1 1 ≤ 1 + xs.length`. -/
lemma maxFreqSortedAux_one_one_le_length [DecidableEq α] (x : α) (xs : List α) :
    maxFreqSortedAux xs x 1 1 ≤ 1 + xs.length := by
  have h_le := maxFreqSortedAux_le_add xs x 1 1 (by omega)
  have h_max : max 1 (1 + xs.length) = 1 + xs.length := by
    apply max_eq_right; omega
  rw [h_max] at h_le
  exact h_le

/-- The maximum frequency in a sorted list does not exceed the list length. -/
lemma maxFreqSorted_le_length [DecidableEq α] (lst : List α) :
    maxFreqSorted lst ≤ lst.length := by
  cases lst with
  | nil => simp [maxFreqSorted]
  | cons x xs =>
    unfold maxFreqSorted
    have h_le := maxFreqSortedAux_le_add xs x 1 1 (by omega)
    have h_max : max 1 (1 + xs.length) = 1 + xs.length := by
      apply max_eq_right; omega
    rw [h_max] at h_le
    have h_len : 1 + xs.length = (x :: xs).length := by
      simp [List.length_cons, add_comm]
    rw [h_len] at h_le
    exact h_le

/-! ### `isStrictMode` — an element that appears strictly more often than any other -/

/-- `x` is a strict mode of `l` if every element `y ≠ x` in `l` appears strictly fewer times
than `x` in `l`. In other words, `x` is the unique element with maximum frequency,
and its count is strictly greater than all others. -/
def isStrictMode {α : Type} [DecidableEq α] (x : α) (l : List α) : Prop :=
  ∀ y ∈ l, y ≠ x → countOcc y l < countOcc x l


lemma isStrictMode_nil {α : Type} [DecidableEq α] (x : α) : isStrictMode x [] := by
  unfold isStrictMode; simp

lemma isStrictMode_singleton {α : Type} [DecidableEq α] (x : α) : isStrictMode x [x] := by
  unfold isStrictMode; intro y hy hne
  have hyx : y = x := by simpa using hy
  rw [hyx] at hne
  exact absurd rfl hne

/-! ### `max?` on `filterMap` results -/

/-- `(l.filterMap f).max? = some m` iff `f a = some m` for some `a ∈ l` and every
value in `l.filterMap f` is ≤ `m`. This combines `max?_eq_some_iff_linearOrder` with
`List.mem_filterMap` for a compact characterization. -/
lemma max_filterMap_eq_some_iff {α β : Type} [LinearOrder β] (f : α → Option β) (l : List α) (m : β) :
    (l.filterMap f).max? = some m ↔ (∃ a ∈ l, f a = some m) ∧ (∀ b ∈ l.filterMap f, b ≤ m) := by
  rw [max?_eq_some_iff_linearOrder, List.mem_filterMap]

/-! ### `countDistinct` — count distinct elements in a list -/

/-- Count the number of distinct elements in a list.
`countDistinct l = |{x | x ∈ l}|`, i.e., the cardinality of the set of elements in `l`.

For example:
* `countDistinct [1, 2, 2, 3, 3, 3] = 3` (the three values 1, 2, 3)
* `countDistinct [] = 0` -/
def countDistinct [DecidableEq α] (l : List α) : Nat :=
  l.dedup.length

lemma countDistinct_nil [DecidableEq α] :
    countDistinct ([] : List α) = 0 := rfl

/-! ### `countDistinctBy` — count distinct values after applying a function -/

/-- Count the number of distinct values obtained by applying `f` to each element of `l`.
Formally, `countDistinctBy f l = |{f x | x ∈ l}|`, i.e., the size of the image of `l` under `f`.

For example:
* `countDistinctBy (fun n => n % 3) [1, 2, 3, 4, 5] = 3` (results are 1, 2, 0)
* `countDistinctBy id [1, 2, 2, 3, 3, 3] = 3` (the three values 1, 2, 3) -/
def countDistinctBy {α β : Type} [DecidableEq β] (f : α → β) (l : List α) : Nat :=
  ((l.map f).eraseDup).length

lemma countDistinctBy_nil {α β : Type} [DecidableEq β] (f : α → β) :
    countDistinctBy f [] = 0 := rfl

/-! ### `countUniqueElems` — count elements appearing exactly once -/

/-- Count how many elements in a list appear exactly once.
Formally, `countUniqueElems xs = |{x ∈ xs | count x xs = 1}|`.

For example:
* `countUniqueElems [1, 2, 2, 3, 3, 3] = 1` (only 1 appears once)
* `countUniqueElems [1, 2, 3] = 3` (all appear exactly once)
* `countUniqueElems [1, 1, 2, 2] = 0` (none appear exactly once) -/
def countUniqueElems [DecidableEq α] (xs : List α) : Nat :=
  xs.countP fun x => xs.count x = 1

/-! ### `countIf` — foldl-based count by predicate -/

/-- Core lemma: `foldl` with addition and a predicate decomposes.
`foldl (fun a' v => if p v then a' + 1 else a') a xs = a + foldl ... 0 xs` -/
lemma foldl_add_pred_eq_add_foldl {α : Type} (p : α → Bool) (a : Nat) (xs : List α) :
    List.foldl (fun a' v => if p v then a' + 1 else a') a xs =
    a + List.foldl (fun a' v => if p v then a' + 1 else a') 0 xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    split
    · rw [ih (a + 1), ih 1]
      omega
    · rw [ih a]

/-- A `foldl` over a list where each step adds 1 when a predicate holds
is equal to the initial accumulator plus the length of the filtered list. -/
lemma foldl_count_pred_eq_add_filter_length {α : Type} (l : List α) (p : α → Bool) (a : Nat) :
    List.foldl (fun acc x => if p x then acc + 1 else acc) a l = a + (l.filter p).length := by
  induction' l with x xs ih generalizing a
  · rfl
  · simp only [List.foldl, List.filter]
    by_cases h : p x
    · simp [h, ih, add_comm, add_left_comm, add_assoc]
    · simp [h, ih]

/-- Count the number of elements in a list that satisfy a predicate.
Uses `foldl` for a tail-recursive implementation.
Contrast with `countIfAux` which uses explicit recursion. -/
def countIf {α : Type} (p : α → Bool) (l : List α) : Nat :=
  l.foldl (fun a v => if p v then a + 1 else a) 0

/-- `countIf` of an empty list is `0`. -/
lemma countIf_nil {α : Type} (p : α → Bool) : countIf p [] = 0 := rfl

/-- `countIf` recursion: processes the head and delegates to the tail. -/
lemma countIf_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    countIf p (x :: xs) = (if p x then 1 else 0) + countIf p xs := by
  simp [countIf, List.foldl]
  split
  · rw [foldl_add_pred_eq_add_foldl p 1 xs]
  · rw [foldl_add_pred_eq_add_foldl p 0 xs]
    simp

/-- The number of elements satisfying predicate `p` is bounded by the list length. -/
lemma countIf_le_length {α : Type} (p : α → Bool) (l : List α) :
    countIf p l ≤ l.length := by
  induction' l with x xs ih
  · simp [countIf]
  · simp [countIf_cons]
    split <;> omega

/-! ### `mem_map_dedup_pair` — membership in dedup then map to pairs -/

/-- Membership in the list `(xs.dedup).map (fun x => (x, f x))` is equivalent
to `a ∈ xs ∧ b = f a`. This is the core lemma used to relate frequency maps
(built via `dedup` then `map` to pairs) to membership in the original list. -/
lemma mem_map_dedup_pair {α β : Type} [DecidableEq α] {xs : List α} {f : α → β} {a : α} {b : β} :
    ((a, b) ∈ ((xs.dedup).map fun x => (x, f x))) ↔ (a ∈ xs ∧ b = f a) := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨x, hx_dedup, hpair⟩
    have hx_mem : x ∈ xs := List.mem_dedup.mp hx_dedup
    have ha_eq : a = x := (congrArg Prod.fst hpair).symm
    have hb_eq : b = f x := (congrArg Prod.snd hpair).symm
    subst ha_eq
    subst hb_eq
    exact ⟨hx_mem, rfl⟩
  · intro ⟨ha_mem, hb_eq⟩
    subst hb_eq
    have ha_dedup : a ∈ xs.dedup := List.mem_dedup.mpr ha_mem
    apply List.mem_map.mpr
    exact ⟨a, ha_dedup, rfl⟩

/-! ### `frequenciesBy` — build a frequency list from a count function -/

/-- Build a frequency list: for each distinct element `w` in `ws`, produce
`(w, count w ws)`. The caller provides the `count` function (e.g., `List.count`)
to compute the frequency of each distinct element.

The result list has no duplicate first entries (each distinct element appears
exactly once) and preserves the order of first occurrence via `dedup`. -/
def frequenciesBy [DecidableEq α] (count : α → List α → Nat) (ws : List α) : List (α × Nat) :=
  (ws.dedup).map (fun w => (w, count w ws))

/-- `freqList f xs` returns a list of `(b, n)` pairs where `b` ranges over the
distinct `f x` values in `xs`, and `n` is the number of `x ∈ xs` such that
`f x = b`. Equivalent to `frequenciesBy countOcc (xs.map f)`. -/
def freqList {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) : List (β × Nat) :=
  let mapped := xs.map f
  mapped.dedup.map (fun b => (b, List.length (mapped.filter (fun x => x = b))))

/-! ### `frequenciesBy` basic properties -/


lemma frequenciesBy_nil {α : Type} [DecidableEq α] (cnt : α → List α → Nat) : frequenciesBy cnt [] = [] := by
  unfold frequenciesBy; simp

/-! ### `frequenciesBy` membership lemmas

These lemmas are stated generically for any `cnt : α → List α → Nat`, so they work
with `countOcc`, `List.count`, or any custom counting function. -/

/-- If an element `x` is in `xs`, then the pair `(x, cnt x xs)` belongs to the frequency map
`frequenciesBy cnt xs`. The frequency map is built from `xs.dedup` and maps each distinct
element to its count via `cnt`. -/
lemma mem_frequenciesBy_of_mem {α : Type} [DecidableEq α] {cnt : α → List α → Nat} {x : α}
    {xs : List α} (hx : x ∈ xs) : (x, cnt x xs) ∈ frequenciesBy cnt xs := by
  have h_mem_unique : x ∈ xs.dedup := by
    rw [List.mem_dedup]
    exact hx
  unfold frequenciesBy
  rw [List.mem_map]
  exact ⟨x, h_mem_unique, rfl⟩

/-- If a pair `p` is in the frequency map `frequenciesBy cnt xs`, then its first component
`p.1` is a member of the original list `xs`. -/
lemma fst_mem_of_mem_frequenciesBy {α : Type} [DecidableEq α] {cnt : α → List α → Nat}
    {p : α × Nat} {xs : List α} (hp : p ∈ frequenciesBy cnt xs) : p.1 ∈ xs := by
  unfold frequenciesBy at hp
  rw [List.mem_map] at hp
  rcases hp with ⟨w, hw, h_eq⟩
  have h_fst_eq : w = p.1 := congrArg Prod.fst h_eq
  rw [← h_fst_eq]
  rw [List.mem_dedup] at hw
  exact hw

/-- If a pair `p` is in the frequency map `frequenciesBy cnt xs`, then the count of `p.1`
computed by `cnt` equals the second component `p.2`. This is a structural property of
`frequenciesBy`: every element of the frequency map is exactly `(w, cnt w xs)` for some `w`. -/
lemma snd_eq_cnt_of_mem_frequenciesBy {α : Type} [DecidableEq α] {cnt : α → List α → Nat}
    {p : α × Nat} {xs : List α} (hp : p ∈ frequenciesBy cnt xs) : cnt p.1 xs = p.2 := by
  unfold frequenciesBy at hp
  rw [List.mem_map] at hp
  rcases hp with ⟨w, hw, rfl⟩
  rfl

/-- If an element has positive count in `l`, then its frequency-count pair belongs to the
frequency mapping of `l`. This is a corollary of `mem_frequenciesBy_of_mem` using `List.count`. -/
lemma mem_frequenciesBy_of_count_pos {α : Type} [DecidableEq α] (l : List α) (k : α)
    (hpos : List.count k l > 0) : (k, List.count k l) ∈ frequenciesBy List.count l :=
  mem_frequenciesBy_of_mem (cnt := List.count) (List.count_pos_iff.mp hpos)

/-- The count of an element `a` in `xs` equals the sum of the second components
of the frequency table `frequenciesBy List.count xs` filtered for entries matching `a`. -/
lemma count_eq_frequenciesBy_sum [DecidableEq α] (xs : List α) (a : α) :
    xs.count a = (((frequenciesBy List.count xs).filter (λ p => p.1 = a)).map Prod.snd).sum := by
  unfold frequenciesBy
  rw [List.filter_map]
  have hcomp : ((fun p => decide (p.1 = a)) ∘ fun x => (x, List.count x xs)) =
      (fun x => decide (x = a)) := by
    ext x; simp
  rw [hcomp]
  simp [Function.comp]
  rw [List.filter_eq]
  rw [List.map_replicate, List.sum_replicate]
  rw [List.count_dedup]
  by_cases hmem : a ∈ xs
  · simp [hmem]
  · have hcount0 : xs.count a = 0 := List.count_eq_zero_of_not_mem hmem
    simp [hmem, hcount0]

/-! ### `frequenciesSortedDesc` — frequency list sorted descending by element -/

/-- Compute frequency counts of each distinct element in `l`, sorted descending by the element
itself (e.g., largest element first). Equivalent to `(frequenciesBy List.count l)` followed by
`mergeSort` with a descending comparator on `Prod.fst`. -/
def frequenciesSortedDesc {α : Type} [DecidableEq α] [LinearOrder α] (l : List α) : List (α × Nat) :=
  (frequenciesBy List.count l).mergeSort (fun p q => decide (p.1 ≥ q.1))

/-! ### `countIn` — count elements of one list that are in another -/

/-- Count how many elements of `xs` appear in `ys`.
`countIn xs ys = |{x ∈ xs | x ∈ ys}|`; equivalently `(xs.filter (· ∈ ys)).length`. -/
def countIn {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  (xs.filter (fun x => x ∈ ys)).length

lemma countIn_nil_left {α : Type} [DecidableEq α] (ys : List α) :
    countIn [] ys = 0 := rfl

lemma countIn_nil_right {α : Type} [DecidableEq α] (xs : List α) :
    countIn xs [] = 0 := by
  simp [countIn]

/-- Relates `countIn` over a mapped list to a direct filter on the original list:
`countIn` applied to `map f xs` against `ys` equals the size of `xs` filtered
by membership of `f x` in `ys`. -/
lemma countIn_map_filter_eq {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) (ys : List β) :
    countIn (xs.map f) ys = (xs.filter (fun x => f x ∈ ys)).length := by
  unfold countIn
  have h_pred_eq : ((fun x : β => decide (x ∈ ys)) ∘ f) = (fun x : α => decide (f x ∈ ys)) := by
    funext x; simp
  calc
    ((xs.map f).filter (fun x => x ∈ ys)).length
        = ((xs.map f).filter (fun x => decide (x ∈ ys) = true)).length := by simp
    _ = (List.map f (xs.filter (fun x => decide (f x ∈ ys) = true))).length := by
      simp [List.filter_map, h_pred_eq]
    _ = (xs.filter (fun x => decide (f x ∈ ys) = true)).length := by simp
    _ = (xs.filter (fun x => f x ∈ ys)).length := by simp

/-! ### `countLe` and `countLess` — count elements ≤ or < a threshold

`countLe l x` returns the number of elements in `l` that are `≤ x`.
`countLess l x` returns the number of elements in `l` that are `< x`. -/

/-- Count how many elements in `l` are `< x`. -/
def countLess {α : Type} [LinearOrder α] : List α → α → Nat
  | [], _ => 0
  | y :: ys, x => (if y < x then 1 else 0) + countLess ys x

/-- Count how many elements in `l` are `≤ x`. -/
def countLe {α : Type} [LinearOrder α] : List α → α → Nat
  | [], _ => 0
  | y :: ys, x => (if y ≤ x then 1 else 0) + countLe ys x


lemma countLess_nil {α : Type} [LinearOrder α] (x : α) : countLess [] x = 0 := rfl


lemma countLe_nil {α : Type} [LinearOrder α] (x : α) : countLe [] x = 0 := rfl

lemma countLess_eq_filter_length {α : Type} [LinearOrder α] (l : List α) (x : α) :
    countLess l x = (List.filter (fun y => decide (y < x)) l).length := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [countLess]
    by_cases h : y < x
    · simp [h, List.filter, ih, add_comm]
    · simp [h, List.filter, ih]

lemma countLe_eq_filter_length {α : Type} [LinearOrder α] (l : List α) (x : α) :
    countLe l x = (List.filter (fun y => decide (y ≤ x)) l).length := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [countLe]
    by_cases h : y ≤ x
    · simp [h, List.filter, ih, add_comm]
    · simp [h, List.filter, ih]

lemma countLess_perm {α : Type} [LinearOrder α] {l₁ l₂ : List α} (h : List.Perm l₁ l₂) (x : α) :
    countLess l₁ x = countLess l₂ x := by
  rw [countLess_eq_filter_length, countLess_eq_filter_length]
  apply List.Perm.length_eq
  let p : α → Bool := fun y => decide (y < x)
  exact List.Perm.filter p h

lemma countLe_perm {α : Type} [LinearOrder α] {l₁ l₂ : List α} (h : List.Perm l₁ l₂) (x : α) :
    countLe l₁ x = countLe l₂ x := by
  rw [countLe_eq_filter_length, countLe_eq_filter_length]
  apply List.Perm.length_eq
  let p : α → Bool := fun y => decide (y ≤ x)
  exact List.Perm.filter p h

/-- If `x ≤ y` for all `y ∈ l`, then `countLess l x = 0`. -/
lemma countLess_of_all_ge {α : Type} [LinearOrder α] (l : List α) (x : α) (h : ∀ y ∈ l, x ≤ y) :
    countLess l x = 0 := by
  induction' l with a l' ih
  · rfl
  · have ha : x ≤ a := h a (by simp)
    have hl' : ∀ y ∈ l', x ≤ y := by
      intro y hy; apply h y; exact List.mem_cons_of_mem _ hy
    simp [countLess, not_lt.mpr ha, ih hl']

/-- In a sorted list `l`, for any index `n < l.length`, the number of elements `< l.get ⟨n, hn⟩` is at most `n`. -/
lemma countLess_sorted_get_le {α : Type} [LinearOrder α] (l : List α) (h_sorted : l.Sorted (· ≤ ·))
    (n : ℕ) (hn : n < l.length) : countLess l (l.get ⟨n, hn⟩) ≤ n := by
  induction' l with a l' ih generalizing n
  · exact (Nat.not_lt_zero _ hn).elim
  · rw [List.sorted_cons] at h_sorted
    rcases h_sorted with ⟨hrel, htail⟩
    cases n with
    | zero =>
      have h_count_zero : countLess l' a = 0 := countLess_of_all_ge l' a hrel
      simp [countLess, h_count_zero]
    | succ n' =>
      have hn' : n' < l'.length := by
        have : n'.succ < (a :: l').length := hn
        simpa using this
      have h_ih := ih htail n' hn'
      have h_val : (a :: l').get ⟨Nat.succ n', hn⟩ = l'.get ⟨n', hn'⟩ := by simp
      rw [h_val]
      rw [countLess]
      by_cases ha_lt : a < l'.get ⟨n', hn'⟩
      · rw [if_pos ha_lt]
        omega
      · rw [if_neg ha_lt]
        omega

/-- In a sorted list `l`, for any index `n < l.length`, at least `n+1` elements are `≤ l.get ⟨n, hn⟩`. -/
lemma countLe_sorted_get_ge {α : Type} [LinearOrder α] (l : List α) (h_sorted : l.Sorted (· ≤ ·))
    (n : ℕ) (hn : n < l.length) : n + 1 ≤ countLe l (l.get ⟨n, hn⟩) := by
  induction' l with a l' ih generalizing n
  · exact (Nat.not_lt_zero _ hn).elim
  · rw [List.sorted_cons] at h_sorted
    rcases h_sorted with ⟨hrel, htail⟩
    cases n with
    | zero =>
      have h_get : (a :: l').get ⟨0, hn⟩ = a := by simp
      rw [h_get]
      simp [countLe, le_refl a]
    | succ n' =>
      have hn' : n' < l'.length := by
        have : n'.succ < (a :: l').length := hn
        simpa using this
      have h_ih := ih htail n' hn'
      have h_mem : l'.get ⟨n', hn'⟩ ∈ l' := List.get_mem l' ⟨n', hn'⟩
      have ha_le : a ≤ l'.get ⟨n', hn'⟩ := hrel (l'.get ⟨n', hn'⟩) h_mem
      have h_val : (a :: l').get ⟨Nat.succ n', hn⟩ = l'.get ⟨n', hn'⟩ := by simp
      rw [h_val]
      rw [countLe]
      rw [if_pos ha_le]
      omega

/-- If `l₁` is a permutation of `l₂`, `l₁` is sorted, and `i.val < k`,
then `countLess l₂ (l₁.get i) < k`. -/
lemma countLess_lt_of_sorted_perm_get {α : Type} [LinearOrder α] {l₁ l₂ : List α} {k : ℕ}
    {i : Fin l₁.length} (h_perm : List.Perm l₁ l₂) (h_sorted : l₁.Sorted (· ≤ ·))
    (hi : i.val < k) : countLess l₂ (l₁.get i) < k := by
  rw [countLess_perm h_perm.symm]
  exact lt_of_le_of_lt (countLess_sorted_get_le l₁ h_sorted i.val i.is_lt) hi

/-- If `l₁` is a permutation of `l₂`, `l₁` is sorted, and `i.val + 1 = k`,
then `k ≤ countLe l₂ (l₁.get i)`. -/
lemma countLe_ge_of_sorted_perm_get {α : Type} [LinearOrder α] {l₁ l₂ : List α} {k : ℕ}
    {i : Fin l₁.length} (h_perm : List.Perm l₁ l₂) (h_sorted : l₁.Sorted (· ≤ ·))
    (hi : i.val + 1 = k) : k ≤ countLe l₂ (l₁.get i) := by
  rw [countLe_perm h_perm.symm, ← hi]
  exact countLe_sorted_get_ge l₁ h_sorted i.val i.is_lt

/-! ### `mostFrequent` — elements achieving the maximum frequency -/

/-- Return the subset of elements from `ws` that achieve the maximum frequency.
That is, `v ∈ mostFrequent ws` iff `v ∈ ws` and `List.count v ws = maxFreq ws`.
The result is `Nodup` by construction (via `dedup`).

For example, `mostFrequent [1, 2, 1, 3, 2, 1] = [1]` (element `1` appears 3 times). -/
def mostFrequent {α : Type} [DecidableEq α] (ws : List α) : List α :=
  (ws.dedup).filter fun w => decide (List.count w ws = maxFreq ws)

/-- `mostFrequent ws` is `Nodup` — there are no duplicate entries. -/
lemma nodup_mostFrequent {α : Type} [DecidableEq α] (ws : List α) :
    (mostFrequent ws).Nodup :=
  List.Nodup.filter _ (List.nodup_dedup ws)

/-- An element `w` belongs to `mostFrequent ws` iff it appears in `ws` and its
count equals the maximum frequency in `ws`. -/
lemma mem_mostFrequent_iff {α : Type} [DecidableEq α] (ws : List α) (w : α) :
    w ∈ mostFrequent ws ↔ w ∈ ws ∧ List.count w ws = maxFreq ws := by
  unfold mostFrequent
  rw [List.mem_filter, List.mem_dedup, decide_eq_true_iff]

/-! ### `elementCounts` — per-element occurrence counts parallel to the list

For each element at position `i` in `lst`, compute how many times that element
appears in `lst`. The result is a list of counts of the same length as `lst`,
where `(elementCounts lst)[i]` = count of `lst[i]` in `lst`.

Example: `elementCounts [a, b, a, c] = [2, 1, 2, 1]`.

Contrast with `frequencies` (one count per distinct element, deduped) and
`countOccurrences` (count of a specific element across the whole list). -/

/-- For each element `x` in `lst`, compute how many times `x` appears in `lst`.
Returns a list of counts parallel to `lst`:
`(elementCounts lst)[i]` = count of `lst[i]` in `lst`.

Uses `filter` and `length` rather than `List.count` to avoid the `BEq` constraint. -/
def elementCounts {α : Type} [DecidableEq α] (lst : List α) : List Nat :=
  lst.map (λ x => (lst.filter (· = x)).length)


lemma elementCounts_nil {α : Type} [DecidableEq α] : elementCounts ([] : List α) = [] := rfl


lemma elementCounts_length {α : Type} [DecidableEq α] (lst : List α) :
    (elementCounts lst).length = lst.length := by
  simp [elementCounts]

/-- The i-th element of `elementCounts lst` equals the length of the sublist of `lst`
containing only elements equal to `lst[i]`. This is the core property linking
the parallel count list back to the original list's element frequencies. -/
lemma elementCounts_getElem_eq_filter_length {α : Type} [DecidableEq α] [Inhabited α]
    (lst : List α) (i : Nat) (hi : i < lst.length) :
    (elementCounts lst)[i]! = (lst.filter (· = lst[i]!)).length := by
  have hi_map : i < (elementCounts lst).length := by
    simpa [elementCounts] using hi
  simp [elementCounts, hi, hi_map, List.getElem_map]

/-! ### `maxByCount` — find element with maximum count in a reference list -/

/-- Iterate through `remaining` (expected to be a sublist of `l`),
comparing the count of each element in `l` against `best`, and return the element
with the maximum count in `l` along with that count.

This is a building block for mode-finding algorithms: given a reference list `l`
and a list of candidates `remaining`, find which candidate has the highest
occurrence count in `l`. The result is both the best element and its count.

For example, `maxByCount [a, b, a, c, b, a] [b, c] a = (a, 3)`. -/
def maxByCount [DecidableEq α] (l : List α) (remaining : List α) (best : α) : α × Nat :=
  match remaining with
  | [] => (best, l.count best)
  | x :: xs =>
    if l.count x > l.count best then
      maxByCount l xs x
    else
      maxByCount l xs best

/-- Correctness specification for `maxByCount`: the returned element's count in `l`
matches the second component, every element in `remaining` has count ≤ the result's count,
and the initial `best` also has count ≤ the result's count. -/
lemma maxByCount_spec [DecidableEq α] (l remaining : List α) (best : α) :
    let result := maxByCount l remaining best
    l.count result.fst = result.snd ∧
    (∀ x ∈ remaining, l.count x ≤ result.snd) ∧
    l.count best ≤ result.snd := by
  induction remaining generalizing best with
  | nil =>
    simp [maxByCount]
  | cons x xs ih =>
    simp [maxByCount]
    by_cases h : l.count x > l.count best
    · simp [h]
      have ih' := ih x
      rcases ih' with ⟨hcnt, hall, hbest⟩
      refine ⟨hcnt, ⟨⟨hbest, hall⟩, ?_⟩⟩
      have hlt : l.count best < l.count x := h
      have hle : l.count best ≤ l.count x := Nat.le_of_lt hlt
      exact Nat.le_trans hle hbest
    · simp [h]
      have ih' := ih best
      rcases ih' with ⟨hcnt, hall, hbest⟩
      refine ⟨hcnt, ⟨⟨?_, hall⟩, hbest⟩⟩
      have hle : l.count x ≤ l.count best := Nat.le_of_not_gt h
      exact Nat.le_trans hle hbest

end List

namespace List

/-! ### `foldl` with conditional addition -/

/-- For a foldl where each step conditionally adds the first projection, the result with a
nonzero initial value equals the initial value plus the result starting from zero. -/
lemma foldl_cond_add_init {β : Type} (l : List (Nat × β)) (p : β → Prop) [DecidablePred p]
    (init : Nat) :
    l.foldl (fun acc pair => if p pair.2 then acc + pair.1 else acc) init =
    init + l.foldl (fun acc pair => if p pair.2 then acc + pair.1 else acc) 0 := by
  induction' l with pair l ih generalizing init
  · rfl
  · simp only [List.foldl]
    have h_distrib : (if p pair.2 then init + pair.1 else init) =
        init + (if p pair.2 then pair.1 else 0) := by
      by_cases h : p pair.2 <;> simp [h]
    have h_zero : (if p pair.2 then (0 : Nat) + pair.1 else 0) =
        (if p pair.2 then pair.1 else 0) := by
      by_cases h : p pair.2 <;> simp [h]
    rw [h_distrib, h_zero]
    rw [ih (init + (if p pair.2 then pair.1 else 0)), ih (if p pair.2 then pair.1 else 0)]
    omega

/-- For a foldl that adds 0 or 1 based on a predicate, the accumulator distributes.
That is, `l.foldl (λ acc x => if P x then acc + 1 else acc) a = a + l.foldl (λ acc x => if P x then acc + 1 else acc) 0`.
This is useful for counting elements that satisfy a predicate while tracking a running total. -/
lemma foldl_add_count {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] (a : Nat) :
    l.foldl (fun acc x => if P x then acc + 1 else acc) a =
    a + l.foldl (fun acc x => if P x then acc + 1 else acc) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    rw [ih (if P y then a + 1 else a), ih (if P y then 1 else 0)]
    split <;> omega

/-- Sum `f x` for each element of `xs` satisfying the boolean predicate `pred`.
Captures the common pattern `∑ {f(x) | x ∈ xs, pred x}`. -/
def sumFilterMap {α : Type u} (f : α → Nat) (pred : α → Bool) (xs : List α) : Nat :=
  xs.foldl (fun acc x => if pred x then acc + f x else acc) 0


theorem sumFilterMap_nil {α : Type u} (f : α → Nat) (pred : α → Bool) :
    sumFilterMap f pred [] = 0 := rfl

/-- The initial accumulator in a conditional-addition fold factors out as a constant term:
`foldl (λ acc x => if pred x then acc + f x else acc) init xs = init + sumFilterMap f pred xs`.
This generalizes `foldl_add_count` (which is the special case `f = λ _ => 1`). -/
lemma sumFilterMap_add_init {α : Type u} (f : α → Nat) (pred : α → Bool) (init : Nat) (xs : List α) :
    xs.foldl (fun acc x => if pred x then acc + f x else acc) init =
    init + sumFilterMap f pred xs := by
  induction' xs with x xs ih generalizing init
  · rfl
  · simp [List.foldl, sumFilterMap]
    split
    · -- case: pred x is true
      rw [ih (init + f x), ih (f x)]
      omega
    · -- case: pred x is false
      exact ih init

/-- A conditional step function `if c x then acc + f x else acc` can be written
as `acc + (if c x then f x else 0)`. This is the key identity for converting
conditional-accumulation folds into additive folds where the predicate controls
a zero/nonzero term. -/
lemma cond_step_eq_add {α : Type} (c : α → Prop) [∀ x, Decidable (c x)] (f : α → Nat) (acc : Nat) (x : α) :
    (if c x then acc + f x else acc) = acc + (if c x then f x else 0) := by
  by_cases hc : c x
  · simp [hc]
  · simp [hc]

/-- Lifting `cond_step_eq_add` to a `foldl` equality: a conditional-accumulation fold
is equal to an additive fold where the condition controls whether `f x` or `0` is added. -/
lemma foldl_cond_step_eq_foldl_add_step {α : Type} (c : α → Prop) [∀ x, Decidable (c x)] (f : α → Nat) (l : List α) (init : Nat) :
    l.foldl (λ acc x => if c x then acc + f x else acc) init =
    l.foldl (λ acc x => acc + (if c x then f x else 0)) init := by
  induction' l with x xs ih generalizing init
  · rfl
  · rw [List.foldl, List.foldl]
    rw [cond_step_eq_add c f init x]
    exact ih _

/-- Pull an outer accumulator into a conditional foldl, converting it to additive form:
`b + l.foldl (if c ... then acc + f ... else acc) 0 = l.foldl (acc + (if c ... then f ... else 0)) b`.
Useful for rearranging nested fold loops. -/
lemma foldl_cond_add_shift {α : Type} (c : α → Prop) [∀ x, Decidable (c x)] (f : α → Nat) (l : List α) (b : Nat) :
    b + l.foldl (λ acc x => if c x then acc + f x else acc) 0 =
    l.foldl (λ acc x => acc + (if c x then f x else 0)) b := by
  have step : (fun (acc : Nat) x => if c x then acc + f x else acc) =
      (fun acc x => acc + (if c x then f x else 0)) := by
    funext acc x; split <;> simp_all
  rw [step]
  have aux (xs : List α) (a : Nat) :
      xs.foldl (fun acc x => acc + (if c x then f x else 0)) a =
        a + (xs.map (fun x => if c x then f x else 0)).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons, ih, Nat.add_assoc]
  simp [aux]

/-! ### `foldl` complement-counting lemmas -/

/-- Counting foldl where matches increment the counter: the result is always ≥ the initial value.
That is, `foldl (λ acc a => if f a = t then acc + 1 else acc) init xs ≥ init`. -/
lemma foldl_count_ge_init {α β : Type} [DecidableEq β] (f : α → β) (t : β) (ls : List α) (init : Nat) :
    ls.foldl (fun acc a => if f a = t then acc + 1 else acc) init ≥ init := by
  induction' ls with x xs ih generalizing init
  · rfl
  · simp [List.foldl]
    by_cases h_eq : f x = t
    · simp [h_eq]
      have h_ih : xs.foldl (fun acc a => if f a = t then acc + 1 else acc) (init + 1) ≥ init + 1 := ih (init + 1)
      omega
    · simp [h_eq]
      exact ih init

/-- If no element satisfies the predicate (i.e., `∀ a, f a ≠ t`), then the counting foldl
returns `init` unchanged. -/
lemma foldl_count_eq_init_of_forall_not {α β : Type} [DecidableEq β] (f : α → β) (t : β)
    (h : ∀ a : α, f a ≠ t) (ls : List α) (init : Nat) :
    ls.foldl (fun acc a => if f a = t then acc + 1 else acc) init = init := by
  induction' ls with x xs ih generalizing init
  · simp
  · have h_ne : f x ≠ t := h x
    rw [List.foldl_cons]
    simp [h_ne, ih]

/-- If the foldl-based count of element `v` exceeds 0, then `v` is in the list.
This is the membership direction for the count-via-foldl pattern. -/
lemma foldl_count_pos_imp_mem {α : Type} [DecidableEq α] (l : List α) (v : α) :
    l.foldl (fun (acc : Nat) (x : α) => if x = v then acc + 1 else acc) 0 > 0 → v ∈ l := by
  induction' l with x xs ih
  · simp
  · simp only [List.foldl_cons]
    by_cases hx : x = v
    · simp [hx]
    · intro h
      have h' : xs.foldl (fun acc x => if x = v then acc + 1 else acc) 0 > 0 := by
        simpa [hx] using h
      have ih' := ih h'
      simp [hx, ih']

/-- For complementary counting folds (one counts matches `f x = t`, the other counts mismatches),
the sum of the two folds equals `a + b + length ls`. Each list element contributes exactly 1
to the combined total regardless of whether it matches. -/
lemma foldl_complement_add {α β : Type} [DecidableEq β] (f : α → β) (t : β) (ls : List α) (a b : Nat) :
    ls.foldl (fun acc x => if f x = t then acc else acc + 1) a +
    ls.foldl (fun acc x => if f x = t then acc + 1 else acc) b = a + b + ls.length := by
  induction ls generalizing a b with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl, List.length_cons]
    by_cases h_eq : f x = t
    · simp [h_eq]
      rw [ih a (b+1)]
      omega
    · simp [h_eq]
      rw [ih (a+1) b]
      omega

/-- Shifting the initial accumulator of a counting `foldl` by 1 is equivalent to adding 1
to the result. This is a structural lemma for the foldl-based count pattern:
`foldl (λ acc x => if x = w then acc + 1 else acc) (init + 1) l = foldl ... init l + 1`. -/
lemma foldl_count_add_one {α : Type u} [DecidableEq α] (l : List α) (w : α) (init : Nat) :
    List.foldl (fun (acc : Nat) (x : α) => if x = w then acc + 1 else acc) (init + 1) l =
    List.foldl (fun (acc : Nat) (x : α) => if x = w then acc + 1 else acc) init l + 1 := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · simpa using ih (init + 1)
    · simpa using ih init

/-! ### `countGe` — count elements greater than or equal to a threshold -/

/-- Count how many elements of `ns` are greater than or equal to `v`.
```
countGe v [x₁, …, xₙ] = |{i | v ≤ xᵢ}|
```
-/
def countGe (v : Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => (if v ≤ x then 1 else 0) + countGe v xs

lemma countGe_nil (v : Nat) : countGe v [] = 0 := rfl

/-- `countGe` distributes over list concatenation. -/
lemma countGe_append (v : Nat) (xs ys : List Nat) :
    countGe v (xs ++ ys) = countGe v xs + countGe v ys := by
  induction xs with
  | nil => simp [countGe]
  | cons x xs ih => simp [countGe, ih, Nat.add_assoc]

/-! ### `countFilter` — count elements satisfying a boolean predicate via `filter` -/

/-- Count the number of elements in `l` that satisfy the boolean predicate `p`.
`countFilter l p = (l.filter p).length`. Equivalent to `List.countP p l`. -/
def countFilter {α : Type} (l : List α) (p : α → Bool) : Nat :=
  (l.filter p).length


lemma countFilter_nil {α : Type} (p : α → Bool) : countFilter ([] : List α) p = 0 := rfl

lemma countFilter_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    countFilter (x :: xs) p = (if p x then 1 else 0) + countFilter xs p := by
  simp [countFilter]
  by_cases h : p x <;> simp [h] <;> omega


lemma countFilter_append {α : Type} (p : α → Bool) (xs ys : List α) :
    countFilter (xs ++ ys) p = countFilter xs p + countFilter ys p := by
  simp [countFilter]

/-- The number of elements satisfying a predicate is at most the list length. -/
lemma countFilter_le_length {α : Type} (l : List α) (p : α → Bool) :
    countFilter l p ≤ l.length := by
  unfold countFilter
  induction' l with h t ih
  · rfl
  · simp only [List.filter, List.length_cons]
    split
    · exact Nat.succ_le_succ ih
    · exact Nat.le_trans ih (Nat.le_succ _)

/-! ### `countOdd` — count odd numbers in a list -/

/-- Count the number of odd numbers in a `List Nat`.
`countOdd [x₁, …, xₙ] = |{i | xᵢ % 2 = 1}|`.
Defined as `countFilter l (fun d => decide (d % 2 = 1))`. -/
def countOdd (l : List Nat) : Nat := countFilter l (fun d => decide (d % 2 = 1))


lemma countOdd_nil : countOdd [] = 0 := rfl

lemma countOdd_cons (x : Nat) (xs : List Nat) :
    countOdd (x :: xs) = (if x % 2 = 1 then 1 else 0) + countOdd xs := by
  simp [countOdd, countFilter_cons]

/-! ### `countLowercase` — count lowercase characters in a `List Char` -/

/-- Count the number of lowercase characters in a `List Char`.
Uses `Char.isLower` which covers all Unicode lowercase characters.
For example, `countLowercase ['a', 'B', 'c', 'D'] = 2`. -/
def countLowercase (l : List Char) : Nat :=
  (l.filter Char.isLower).length


lemma countLowercase_nil : countLowercase [] = 0 := rfl

lemma countLowercase_cons (x : Char) (xs : List Char) :
    countLowercase (x :: xs) = (if Char.isLower x then 1 else 0) + countLowercase xs := by
  simp [countLowercase]
  by_cases h : Char.isLower x <;> simp [h] <;> omega

/-! ### `listCount` — count elements satisfying a boolean predicate -/

/-- Count elements in a list that satisfy a boolean predicate.
`listCount p [x₁, …, xₙ] = |{i | p xᵢ = true}|`.
Defined via `sum` and `map` for convenient algebraic manipulation;
behaviorally equivalent to `List.countP`. -/
def listCount {α : Type} (p : α → Bool) (l : List α) : Nat :=
  (l.map (fun x => if p x then 1 else 0)).sum

lemma listCount_nil {α : Type} (p : α → Bool) : listCount p [] = 0 := rfl

lemma listCount_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    listCount p (x :: xs) = (if p x then 1 else 0) + listCount p xs := by
  simp [listCount]

/-! ### `countOccurrences` — count occurrences of a specific element -/


lemma countOccurrences_nil [DecidableEq α] (a : α) : countOccurrences a [] = 0 := rfl

/-- `countOccurrences` decomposes at the head of the list. -/
lemma countOccurrences_cons [DecidableEq α] (a x : α) (xs : List α) :
    countOccurrences a (x :: xs) =
    (if x = a then 1 else 0) + countOccurrences a xs := by
  unfold countOccurrences
  simp only [List.filter_cons, List.length_cons]
  by_cases h : x = a
  · simp [h]; omega
  · simp [h]

/-- `countOccurrences` is equivalent to `listCount (decide (· = a))`. -/
lemma countOccurrences_eq_listCount [DecidableEq α] (a : α) (l : List α) :
    countOccurrences a l = listCount (fun x => decide (x = a)) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [countOccurrences_cons, listCount_cons, ih]
    by_cases h : x = a <;> simp [h]

/-- If an element does not appear in a list, its occurrence count is zero. -/
lemma countOccurrences_eq_zero_of_not_mem [DecidableEq α] {a : α} {l : List α} (h : a ∉ l) :
    countOccurrences a l = 0 := by
  unfold countOccurrences
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mem_cons] at h
    obtain ⟨hne, hnotmem⟩ := h
    by_cases hxeq : x = a
    · exfalso; exact hne hxeq.symm
    · simp [List.filter_cons, hxeq, ih hnotmem]

/-! ### `countOccurrencesB` — count occurrences via `BEq` -/

/-- Count occurrences of `a` in `l` using `BEq` (boolean equality).
`countOccurrencesB a [x₁, …, xₙ] = |{i | xᵢ == a}|`.

This is the `BEq`-based counterpart of `countOccurrences`, which requires `DecidableEq`.
When `DecidableEq α` is available, use `countOccurrences` for better lemma support;
otherwise, `countOccurrencesB` works with only `BEq α`. -/
def countOccurrencesB {α : Type} [BEq α] (a : α) (l : List α) : Nat :=
  (l.filter (· == a)).length


lemma countOccurrencesB_nil {α : Type} [BEq α] (a : α) : countOccurrencesB a [] = 0 := by
  simp [countOccurrencesB]

/-- `countOccurrencesB` in terms of `List.filter` and `List.length`. -/
lemma countOccurrencesB_eq {α : Type} [BEq α] (a : α) (l : List α) :
    countOccurrencesB a l = (l.filter (· == a)).length := rfl

/-- When `DecidableEq α` is available, `countOccurrences` and `countOccurrencesB` coincide. -/
lemma countOccurrences_eq_countOccurrencesB [DecidableEq α] (a : α) (l : List α) :
    countOccurrences a l = countOccurrencesB a l := by
  unfold countOccurrences countOccurrencesB
  have h : (fun (x : α) => decide (x = a)) = (fun x => x == a) := by
    ext x; by_cases h : x = a <;> simp [h]
  rw [h]

end List

namespace List


/-! ### Counting elements satisfying a predicate -/

/-- Count the number of elements in `l` that satisfy the predicate `p`.
Uses `DecidablePred` to bridge from `Prop` to `Bool` via `decide`.
More general than `countGt` (which counts elements exceeding a threshold)
and `countElem` (which counts occurrences of a specific value). -/
def countBy {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : Nat := (l.filter p).length

/-- `countBy` of an empty list is always zero. -/

lemma countBy_nil {α : Type} (p : α → Prop) [DecidablePred p] : countBy [] p = 0 := by
  simp [countBy]

/-- `countBy` for a cons: the count for `x :: xs` is the count for `xs` plus 1 if `p x` holds. -/
lemma countBy_cons {α : Type} (x : α) (xs : List α) (p : α → Prop) [DecidablePred p] :
    countBy (x :: xs) p = countBy xs p + (if p x then 1 else 0) := by
  by_cases h : p x
  · simp [countBy, h]
  · simp [countBy, h]

/-- `countBy` distributes over append: `countBy (xs ++ ys) p = countBy xs p + countBy ys p`. -/
lemma countBy_append {α : Type} (xs ys : List α) (p : α → Prop) [DecidablePred p] :
    countBy (xs ++ ys) p = countBy xs p + countBy ys p := by
  induction xs with
  | nil => simp [countBy]
  | cons x xs ih =>
    simp [countBy_cons, ih]
    by_cases h : p x
    · simp [h, add_comm, add_assoc]
    · simp [h]

/-! ### `countWhereProp` — noncomputable count via classical decidability -/

/-- Count the number of elements in `xs` that satisfy the `Prop` predicate `pred`,
using `Classical` decidability. This is the noncomputable counterpart to `countBy`,
which requires a `DecidablePred` instance.
Prefer `countBy` when decidability is available; use `countWhereProp` in proof contexts
where decidability cannot be (or is not worth) establishing. -/
noncomputable def countWhereProp {α : Type} (pred : α → Prop) (xs : List α) : Nat :=
  open Classical in
  (List.filter (fun x => decide (pred x)) xs).length

/-- `countWhereProp` of an empty list is always zero. -/

lemma countWhereProp_nil {α : Type} (pred : α → Prop) : countWhereProp pred [] = 0 := by
  simp [countWhereProp]

/-! ### Counting elements satisfying a `Bool` predicate -/

/-- Count the number of elements in `l` that satisfy the `Bool` predicate `p`.
This is the `Bool` counterpart to `countBy`, which uses a `Prop` predicate
with `DecidablePred`. Prefer `countWhere` when the predicate is naturally
a `Bool` (e.g., from `filter`, `all`, `any`). -/
def countWhere {α : Type} (p : α → Bool) (l : List α) : Nat :=
  (l.filter p).length

/-- `countWhere` of an empty list is always zero. -/

lemma countWhere_nil {α : Type} (p : α → Bool) : countWhere p [] = 0 := by
  simp [countWhere]

/-- `countWhere` for a cons: the count for `x :: xs` is the count for `xs` plus `(if p x then 1 else 0)`. -/
lemma countWhere_cons {α : Type} (x : α) (xs : List α) (p : α → Bool) :
    countWhere p (x :: xs) = countWhere p xs + (if p x then 1 else 0) := by
  simp [countWhere]
  by_cases h : p x
  · simp [h]
  · simp [h]

/-- `countWhere` distributes over append: `countWhere p (xs ++ ys) = countWhere p xs + countWhere p ys`. -/
lemma countWhere_append {α : Type} (xs ys : List α) (p : α → Bool) :
    countWhere p (xs ++ ys) = countWhere p xs + countWhere p ys := by
  induction xs with
  | nil => simp [countWhere]
  | cons x xs ih =>
    simp [countWhere_cons, ih]
    by_cases h : p x
    · simp [h, add_comm, add_assoc]
    · simp [h]

/-- `countWhere` for a singleton list: `countWhere p [x] = (if p x then 1 else 0)`. -/

lemma countWhere_singleton {α : Type} (p : α → Bool) (x : α) : countWhere p [x] = (if p x then 1 else 0) := by
  simp [countWhere, List.filter_cons, List.filter_nil, List.length_cons, List.length_nil]
  split <;> rfl

/-- `countWhere` with a `Bool` predicate is equivalent to `countBy` with `decide`. -/
lemma countWhere_eq_countBy {α : Type} (p : α → Bool) (l : List α) :
    countWhere p l = countBy l (λ x => p x) := by
  simp [countWhere, countBy]

/-- The `Bool` version `countWhere` and the `Prop` version `countBy` are interchangeable
via `by decide` when used with closed terms. -/
lemma countWhere_of_decide {α : Type} (q : α → Prop) [DecidablePred q] (l : List α) :
    countWhere (λ x => decide (q x)) l = countBy l q := by
  simp [countWhere, countBy]



/-! ### Counting elements greater than a threshold -/

/-- Count the number of elements in `l` that are strictly greater than `threshold`. -/
def countGt {α : Type} [LT α] [DecidableRel (α := α) (· > ·)] (l : List α) (threshold : α) : Nat :=
  (l.filter (fun h => h > threshold)).length

theorem countGt_nil {α : Type} [LT α] [DecidableRel (α := α) (· > ·)] (threshold : α) :
    countGt ([] : List α) threshold = 0 := rfl

theorem countGt_append {α : Type} [LT α] [DecidableRel (α := α) (· > ·)] (xs ys : List α)
    (threshold : α) : countGt (xs ++ ys) threshold = countGt xs threshold + countGt ys threshold := by
  simp [countGt, List.filter_append, List.length_append]

/-- Count the number of elements in `l` that are strictly less than `threshold`.
This is the companion of `countGt`: where `countGt l t` counts elements `> t`,
`countLt l t` counts elements `< t`. -/
def countLt {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (l : List α) (threshold : α) : Nat :=
  (l.filter (fun h => h < threshold)).length


/-- If the head equals the target, `countElem w (w :: l) = countElem w l + 1`. -/
lemma countElem_cons_eq {α : Type} [DecidableEq α] (w : α) (l : List α) :
    countElem w (w :: l) = countElem w l + 1 := by
  simp [countElem, List.foldl_cons]
  simpa using foldl_count_add_one l w 0

/-- If the head does not equal the target, `countElem w (x :: l) = countElem w l`. -/
lemma countElem_cons_ne {α : Type} [DecidableEq α] (x : α) (l : List α) (w : α) (h : x ≠ w) :
    countElem w (x :: l) = countElem w l := by
  simp [countElem, List.foldl_cons, h]

/-- Net count: the number of occurrences of `x` minus occurrences of `y` in a list.
Uses truncated subtraction (capped at 0). -/
def netCount {α : Type} (x y : α) (s : List α) [BEq α] : Nat :=
  s.count x - s.count y



/-! ### Counting elements with odd values -/

/--
Counts the number of distinct elements in a list `l` for which `f a` is odd (i.e., `f a % 2 = 1`).
Works on any `List α` with `DecidableEq α`. Only distinct elements are counted:
if a value appears multiple times in `l`, it contributes at most 1 to the result.

This generalizes `oddCountList` which uses the list's own count as `f`.
-/
def oddCountBy {α : Type} [DecidableEq α] (l : List α) (f : α → Nat) : Nat :=
  (l.eraseDup).foldl (fun acc a => if f a % 2 = 1 then acc + 1 else acc) 0


lemma oddCountBy_nil {α : Type} [DecidableEq α] (f : α → Nat) : oddCountBy ([] : List α) f = 0 := rfl

/--
Counts the number of distinct elements in a list that appear an odd number of times.
Specialization of `oddCountBy` using `l.count` as the counting function.
-/
def oddCountList {α : Type} [DecidableEq α] (l : List α) : Nat :=
  oddCountBy l (l.count ·)


lemma oddCountList_nil {α : Type} [DecidableEq α] : oddCountList ([] : List α) = 0 := rfl


end List

namespace List

/-! ### Hamming distance / mismatch count between equal-length lists -/

/-- Count the number of positions at which two lists (of equal length) differ.
If the lists have different lengths, extra elements from the longer list are ignored
(since `zip` truncates to the shorter length). -/
def countMismatches {α : Type u} [DecidableEq α] (l1 l2 : List α) : Nat :=
  ((List.zip l1 l2).filter (fun p : α × α => p.1 ≠ p.2)).length

/-! ### Erase and Nodup -/

/-- Taking a prefix of a `Nodup` list preserves `Nodup`. -/
lemma Nodup.take {α : Type _} {l : List α} (h : l.Nodup) (k : Nat) : (l.take k).Nodup :=
  h.sublist (List.take_sublist k l)

/-- In a Nodup list, an element is not in its own erased version. -/
lemma not_mem_erase_self_nodup {α : Type} [DecidableEq α] {a : α} {l : List α}
    (hn : l.Nodup) : a ∉ l.erase a := by
  induction l generalizing a with
  | nil => simp
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hn with ⟨hd_notin_tl, hn_tl⟩
    by_cases heq : hd = a
    · subst heq
      rw [List.erase_cons_head]
      exact hd_notin_tl
    · have h_beq : ¬ ((hd == a) = true) := by simp [heq]
      rw [List.erase_cons_tail h_beq]
      simp [Ne.symm heq, ih hn_tl]

/-! ### Hamming distance / mismatch count between equal-length lists -/

/-- A list has zero mismatches with itself. -/

lemma countMismatches_self {α : Type u} [DecidableEq α] (l : List α) : countMismatches l l = 0 := by
  unfold countMismatches
  induction' l with x xs ih
  · rfl
  · have hzip : List.zip (x :: xs) (x :: xs) = (x, x) :: List.zip xs xs := rfl
    rw [hzip]
    simpa using ih

/-- `countMismatches l1 l2 ≤ min l1.length l2.length`. -/
lemma countMismatches_le_length {α : Type u} [DecidableEq α] (l1 l2 : List α) :
    countMismatches l1 l2 ≤ min l1.length l2.length := by
  rw [countMismatches]
  calc
    ((List.zip l1 l2).filter (fun p : α × α => p.1 ≠ p.2)).length ≤ (List.zip l1 l2).length :=
      List.length_filter_le _ _
    _ = min l1.length l2.length := by simp

/-! ### `countExactMatches` — count positions where two lists agree -/

/-- Count the number of positions at which two lists have equal elements.
The dual of `countMismatches`. If the lists have different lengths, extra elements
from the longer list are ignored (since `zip` truncates to the shorter length). -/
def countExactMatches {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  ((List.zip xs ys).filter (fun p => p.1 = p.2)).length

/-- `countExactMatches` is bounded above by the length of the first list. -/
lemma countExactMatches_le_length {α : Type} [DecidableEq α] (xs ys : List α) :
    countExactMatches xs ys ≤ xs.length := by
  unfold countExactMatches
  have hfilter := List.length_filter_le (fun p => decide (p.1 = p.2)) (List.zip xs ys)
  have hzip : (List.zip xs ys).length = xs.length ⊓ ys.length := List.length_zip _ _
  have hmin : xs.length ⊓ ys.length ≤ xs.length := Nat.min_le_left _ _
  calc
    ((List.zip xs ys).filter (fun p => p.1 = p.2)).length ≤ (List.zip xs ys).length := hfilter
    _ = xs.length ⊓ ys.length := hzip
    _ ≤ xs.length := hmin

/-! ### Alternating pattern mismatch count -/

/-- Count the number of positions in `xs` that deviate from an alternating pattern
`start, other, start, other, ...`. Fully general: works over any `List α` with `[DecidableEq α]`
and any two alternating values `start` and `other`.

For example, `alternatingMismatches ['0','1','0','0'] '0' '1' = 1` (the last '0' should be '1'),
and `alternatingMismatches ['0','1','0','0'] '1' '0' = 3` (only position 1 matches; expected '1','0','1','0').

This is useful for problems involving binary strings that need to be made alternating. -/
def alternatingMismatches {α : Type} [DecidableEq α] (xs : List α) (start other : α) : Nat :=
  (xs.zipIdx).foldl
    (fun acc ⟨c, i⟩ =>
      let expected : α :=
        if i % 2 = 0 then start else other
      if c = expected then acc else acc + 1)
    0

/-! ### Interleaving from both ends -/

/-- Given a list, produce a new list of the same length by interleaving
elements from the front (even indices) and the back (odd indices).
Uses `List.getD` with a default from `Inhabited`.

For example, `interleaveEnds [1,2,3,4,5] = [1,5,2,4,3]`.
Also known as "alternating" in some problem contexts. -/
def interleaveEnds {α : Type} [Inhabited α] (lst : List α) : List α :=
  let n := lst.length
  (List.range n).map (fun i =>
    if i % 2 = 0 then
      lst.getD (i / 2) default
    else
      lst.getD (n - 1 - (i / 2)) default)

/-- `interleaveEnds` preserves the length of the original list. -/

lemma interleaveEnds_length {α : Type} [Inhabited α] (lst : List α) :
    (interleaveEnds lst).length = lst.length := by
  simp [interleaveEnds, List.length_map, List.length_range]

/-- `interleaveEnds` of the empty list is the empty list. -/

lemma interleaveEnds_nil {α : Type} [Inhabited α] : interleaveEnds ([] : List α) = [] := by
  simp [interleaveEnds]

/-- `interleaveEnds` of a singleton list is the list itself. -/

lemma interleaveEnds_singleton {α : Type} [Inhabited α] (a : α) : interleaveEnds [a] = [a] := by
  unfold interleaveEnds
  simp [show List.range 1 = [0] by decide]

end List


namespace List

/-! # Frequency Map using Association Lists

Operations for building and manipulating frequency maps represented as
association lists `List (α × Nat)`. Each key appears at most once in the list,
and the value is its count. A count of `0` means the key is absent from the map.

These are useful for problems that need to track and update frequencies dynamically
(e.g., greedy algorithms that consume elements by decrementing counts).
-/

/-- Look up the count for key `k` in a frequency map. Returns `0` if not found. -/
def freqLookup {α : Type} [DecidableEq α] (m : List (α × Nat)) (k : α) : Nat :=
  match m with
  | [] => 0
  | (k', c) :: t => if k = k' then c else freqLookup t k

/-- Set the count for key `k` to `c` in a frequency map. Removes the entry if `c = 0`. -/
def freqSet {α : Type} [DecidableEq α] (m : List (α × Nat)) (k : α) (c : Nat) : List (α × Nat) :=
  match m with
  | [] =>
      if c = 0 then [] else [(k, c)]
  | (k', c') :: t =>
      if k = k' then
        if c = 0 then t else (k, c) :: t
      else
        (k', c') :: freqSet t k c

/-- Increment the count for key `k` by `1`. -/
def freqInc {α : Type} [DecidableEq α] (m : List (α × Nat)) (k : α) : List (α × Nat) :=
  let c := freqLookup m k
  freqSet m k (c + 1)

/-- Decrement the count for key `k` by `1`. No-op if count is already `0`. -/
def freqDec {α : Type} [DecidableEq α] (m : List (α × Nat)) (k : α) : List (α × Nat) :=
  let c := freqLookup m k
  if c = 0 then m else freqSet m k (c - 1)

/-- Build a frequency map from a list of elements.
Each distinct element `x` appears as a pair `(x, count)` in the result.
Elements keep the order of their first occurrence. -/
def toFreqMap {α : Type} [DecidableEq α] (xs : List α) : List (α × Nat) :=
  xs.foldl (fun acc x => freqInc acc x) []

/-- Counts the frequency of each element in a list, returning a list of
`(element, count)` pairs in order of **last** occurrence (when an element is
seen again, it is moved to the end).

In contrast to `toFreqMap` (which preserves first-occurrence order), this
places each element at the position of its final occurrence. -/
def countFreq {α : Type} [DecidableEq α] (ws : List α) : List (α × Nat) :=
  ws.foldl (fun acc w =>
    match acc.find? (fun p => p.1 = w) with
    | some ⟨_, n⟩ =>
        let acc' := acc.filter (fun p => p.1 ≠ w)
        acc' ++ [(w, n + 1)]
    | none => acc ++ [(w, 1)]) []


theorem countFreq_nil {α : Type} [DecidableEq α] : countFreq ([] : List α) = [] := rfl

/-! ### Association list lookup with default

`lookupD` extends `List.lookup` (which returns `Option`) by taking an explicit
`default` value returned when the key is not found. -/

/-- Look up a key in an association list, returning `default` if the key is not found.
`lookupD default key [(k₁, v₁), (k₂, v₂), …]` returns the first `vᵢ` where `kᵢ == key`,
or `default` if no such pair exists. -/
def lookupD {α β : Type} [BEq α] (default : β) (key : α) : List (α × β) → β
  | [] => default
  | (k, v) :: t => if k == key then v else lookupD default key t


lemma lookupD_nil {α β : Type} [BEq α] (default : β) (key : α) :
    lookupD default key [] = default := rfl


lemma lookupD_cons {α β : Type} [BEq α] (k : α) (v : β) (t : List (α × β)) (default : β) (key : α) :
    lookupD default key ((k, v) :: t) = if k == key then v else lookupD default key t := rfl

/-- When the key does not match the first entry, `lookupD` recurses into the tail. -/
lemma lookupD_cons_ne {α β : Type} [DecidableEq α] (k : α) (v : β) (t : List (α × β))
    (default : β) (key : α) (h : key ≠ k) :
    lookupD default key ((k, v) :: t) = lookupD default key t := by
  simp [lookupD_cons, h.symm]

/-! ### Association list find-and-remove

`findAndRemove key alist` searches for `key` in the association list. If found,
returns `some (value, rest)` where `value` is the associated value and `rest` is
the list with that key-value pair removed. If not found, returns `none`.

This is a combined lookup + removal, useful for caches (LRU, eviction policies)
and any algorithm that needs to extract and re-insert entries at the head. -/

/-- Search for a key in a list of key-value pairs.
If found, return the associated value together with the list
where that pair has been removed. Works for any decidable key type. -/
def findAndRemove {α β : Type} [DecidableEq α] (key : α) : List (α × β) → Option (β × List (α × β))
  | [] => none
  | (k, v) :: t =>
      if k = key then
        some (v, t)
      else
        match findAndRemove key t with
        | none => none
        | some (v', rest) => some (v', (k, v) :: rest)

/-! ### `maxCount` — maximum count in a frequency map

`maxCount` finds the maximum count (second component) in a frequency association
list `List (α × Nat)`. Returns `0` for the empty list. Contrast with `maxFreq`
(in `general/List/Count.lean`) which operates directly on the original list using
`List.count` rather than on a precomputed frequency map. -/

/-- Find the maximum count in a frequency list. Returns 0 for empty list. -/
def maxCount {α : Type} (freqs : List (α × Nat)) : Nat :=
  match freqs with
  | [] => 0
  | (_, c) :: t => Nat.max c (maxCount t)

/-- Build a frequency map by first applying `f` to each element of `xs`, then counting
distinct results. For each distinct `b` in the image of `f` over `xs`, returns `(b, count)`.

This generalizes `toFreqMap` by allowing a pre-mapping function `f : α → β` before counting,
so you can count derived values (e.g., lowercased strings, digits of numbers, etc.). -/
def frequencyMap [DecidableEq β] (f : α → β) (xs : List α) : List (β × Nat) :=
  let mapped := xs.map f
  mapped.eraseDup.map (fun b => (b, mapped.count b))

end List

namespace List

/-! ### `length_filter_append` — filter length distributes over append -/

/-- The length of `filter p (xs ++ ys)` equals the sum of the lengths of
`filter p xs` and `filter p ys`. This is the analogue of `countP_add` for
`filter` length, useful when counting matches across concatenated lists. -/
lemma length_filter_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (List.filter p (xs ++ ys)).length = (List.filter p xs).length + (List.filter p ys).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
    by_cases h : p x
    · simp [h]; omega
    · simp [h]

/-! ### `countMatches` — count elements matching a binary predicate with fixed first argument -/

/-- Count elements `j ∈ js` such that `p i j` holds, for a fixed `i : α`.
`countMatches p i js = |{j ∈ js | p i j = true}|`.

This is the counting analogue of `sumOver`: where `sumOver f a xs` sums `f a x` over `xs`,
`countMatches p i js` counts those `j` for which the binary predicate `p` returns `true`. -/
def countMatches {α β : Type} (p : α → β → Bool) (i : α) (js : List β) : Nat :=
  match js with
  | [] => 0
  | j :: js' => (if p i j then 1 else 0) + countMatches p i js'

/-- `countMatches` is equivalent to `(List.filter (p i) js).length`.
This connects the structural definition to the standard List API. -/
lemma countMatches_eq {α β : Type} (p : α → β → Bool) (i : α) (js : List β) :
    countMatches p i js = (List.filter (p i) js).length := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    unfold countMatches
    by_cases h : p i j
    · simp [h, ih]; omega
    · simp [h, ih]

/-! ### `countAllPairs` — count all matching pairs across two lists -/

/-- Count all pairs `(i, j) ∈ is × js` such that `p i j` holds.
`countAllPairs p is js = |{(i, j) ∈ is × js | p i j = true}|`.

Decomposes as `∑_{i ∈ is} countMatches p i js`. -/
def countAllPairs {α β : Type} (p : α → β → Bool) (is : List α) (js : List β) : Nat :=
  match is with
  | [] => 0
  | i :: is' => countMatches p i js + countAllPairs p is' js

/-- `countAllPairs` over an empty first list is always zero. -/

lemma countAllPairs_nil {α β : Type} (js : List β) (p : α → β → Bool) : countAllPairs p [] js = 0 := rfl

/-- `countAllPairs` recurses on the first list:
`countAllPairs p (i :: is) js = countMatches p i js + countAllPairs p is js`. -/
lemma countAllPairs_cons {α β : Type} (i : α) (is : List α) (js : List β) (p : α → β → Bool) :
    countAllPairs p (i :: is) js = countMatches p i js + countAllPairs p is js := rfl

/-! ### `countPairs` — count ordered pairs from a single list satisfying a predicate -/

/-- Count the number of ordered pairs `(x, y)` drawn from `xs` that satisfy the Boolean predicate `p`.
    This is `|{ (x, y) ∈ xs × xs | p(x, y) }|`.

    Contrast with `countAllPairs p is js` which counts pairs across two potentially different lists
    `is` and `js` using a curried binary predicate `α → β → Bool`. `countPairs` works on a single list
    and uses an uncurried predicate `α × α → Bool` (equivalent to `countAllPairs (fun a b => p (a, b)) xs xs`). -/
def countPairs {α : Type} (xs : List α) (p : α × α → Bool) : Nat :=
  List.length (List.filter p (List.product xs xs))

/-- Count unordered pairs from `xs` satisfying a symmetric predicate `p`,
using cartesian product and dividing the ordered-pair count by 2.

This computes `|{ {a, b} | a, b ∈ xs ∧ p (a, b) }|` assuming `p` is symmetric
(so each unordered pair contributes two ordered pairs) and self-pairs are not counted.
Defined as `(countPairs xs p) / 2`. -/
def countUnorderedPairs {α : Type} (xs : List α) (p : α × α → Bool) : Nat :=
  (countPairs xs p) / 2


theorem countUnorderedPairs_def {α : Type} (xs : List α) (p : α × α → Bool) :
    countUnorderedPairs xs p = (countPairs xs p) / 2 := rfl

/-! ### `anyDistinctPair` — check existence of a distinct pair satisfying a predicate -/

/-- Check whether there exist two distinct elements `w₁` and `w₂` in the list `l`
such that `p w₁ w₂` holds. The condition `w₁ ≠ w₂` ensures we only consider pairs
of distinct positions (not necessarily distinct values — elements at different
indices are treated as distinct candidates).

This is the `Bool`-valued existence checker; for the `Prop`-valued equivalence,
see `anyDistinctPair_eq_true_iff`. -/
def anyDistinctPair {α : Type} [DecidableEq α] (p : α → α → Bool) (l : List α) : Bool :=
  l.any (λ w₁ =>
    l.any (λ w₂ =>
      (decide (w₁ ≠ w₂) && p w₁ w₂)))

/-- `anyDistinctPair p l` is `true` iff there exist two distinct elements `w₁` and `w₂`
in `l` (at distinct positions) such that `p w₁ w₂ = true`. -/
theorem anyDistinctPair_eq_true_iff {α : Type} [DecidableEq α] (p : α → α → Bool) (l : List α) :
    (anyDistinctPair p l = true ↔
     ∃ w₁ ∈ l, ∃ w₂ ∈ l, w₁ ≠ w₂ ∧ p w₁ w₂ = true) := by
  unfold anyDistinctPair
  simp [List.any_eq_true, Bool.and_eq_true, decide_eq_true_iff]

/-! ### `countTriplesWhere` — count triples satisfying a ternary predicate -/

/-- Count the number of triples `(i, j, k)` with `0 ≤ i, j, k < n` satisfying a ternary
Boolean predicate `p : Nat → Nat → Nat → Bool`. Defined as a triple nested fold over
`List.range n`.

Contrast with `countPairs` (for ordered pairs from a single list) and `countAllPairs`
(for pairs across two lists). -/
def countTriplesWhere (n : Nat) (p : Nat → Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i =>
    (List.range n).foldl (fun acc' j =>
      (List.range n).foldl (fun acc'' k =>
        if p i j k then acc'' + 1 else acc'')
        acc')
      acc) 0


lemma countTriplesWhere_zero (p : Nat → Nat → Nat → Bool) : countTriplesWhere 0 p = 0 := by
  unfold countTriplesWhere
  simp

/-! ### `length_filter_map_pair` — filter length over a mapped pair list -/

/-- When `bs` is mapped to `(a, b)` pairs and then filtered by a binary predicate `p`,
the length of the result equals the length of filtering `bs` by `p a` directly.
This lemma bridges product-based and element-based counting for binary predicates. -/
lemma length_filter_map_pair {α β : Type} (p : α → β → Bool) (a : α) (bs : List β) :
    (List.filter (fun (x : α × β) => p x.1 x.2) (List.map (fun b => (a, b)) bs)).length =
    (List.filter (p a) bs).length := by
  have h := List.filter_map (f := fun b : β => (a, b)) (l := bs) (p := fun (x : α × β) => p x.1 x.2)
  calc
    (List.filter (fun (x : α × β) => p x.1 x.2) (List.map (fun b => (a, b)) bs)).length
    = (List.map (fun b => (a, b)) (List.filter ((fun (x : α × β) => p x.1 x.2) ∘ (fun b => (a, b))) bs)).length := by
      rw [h]
    _ = (List.filter ((fun (x : α × β) => p x.1 x.2) ∘ (fun b => (a, b))) bs).length := by simp
    _ = (List.filter (p a) bs).length := by
      apply congrArg (fun g => (List.filter g bs).length)
      ext b
      simp

end List

namespace List

/-! ### Filter / Count interaction -/

/-- If an element does not satisfy a predicate, its count in the filtered list is zero.
This is the companion to `List.count_filter` (which covers the `true` case). -/
lemma count_filter_of_false {α : Type _} [BEq α] [LawfulBEq α] {p : α → Bool} {a : α} {l : List α}
    (h : p a = false) : List.count a (List.filter p l) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hmem
  rcases List.mem_filter.mp hmem with ⟨_, hp⟩
  rw [h] at hp
  simp at hp

end List

namespace List

/-! ### Hamming distance -/

/-- Hamming distance between two lists: the number of positions where the lists differ.
Uses `zipWith` to compare elements positionally and counts the mismatches.
If the lists have different lengths, only the common prefix is compared. -/
def hammingDistList {α : Type} [DecidableEq α] (l₁ l₂ : List α) : Nat :=
  List.sum (List.zipWith (fun a b => if a = b then 0 else 1) l₁ l₂)

end List

namespace List

/-! ### Counting contiguous subarrays -/

/-- Count the contiguous subarrays of `nums` that satisfy `p`. -/
def countSubarraysWhere {α : Type} (nums : List α) (p : List α → Bool) : Nat :=
  listCount p (allSubarrays nums)

lemma countSubarraysWhere_nil {α : Type} (p : List α → Bool) :
    countSubarraysWhere [] p = 0 := by
  first
  | (solve
    | rfl
    | simp_all [countSubarraysWhere]
    | omega
    | aesop
    | simp_all [countSubarraysWhere, List.foldl, List.foldr]
    | simp_all [countSubarraysWhere, Nat.absDiff])

/-- Count contiguous subarrays whose number of elements satisfying `p`, modulo `mod`, is `k`. -/
def countSubarraysModCount {α : Type} (l : List α) (p : α → Prop)
    [DecidablePred p] (mod k : Nat) : Nat :=
  let n := l.length
  ((Finset.subarrayIndexPairs n).filter fun (ij : Nat × Nat) =>
    let sub := (l.drop ij.1).take (ij.2 + 1 - ij.1)
    let cnt := sub.countBy p
    cnt % mod = k
  ).card

lemma countSubarraysModCount_nil {α : Type} (p : α → Prop)
    [DecidablePred p] (mod k : Nat) : countSubarraysModCount [] p mod k = 0 := by
  unfold countSubarraysModCount
  simp [Finset.subarrayIndexPairs]

end List
