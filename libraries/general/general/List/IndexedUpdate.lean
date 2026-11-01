import general.List.Slicing

namespace List


/-! ### Element removal -/

/-- Remove the element at index `i` from `l`. Returns the original list if `i` is out of bounds
(since `take` and `drop` clamp to the list length). -/
def removeAt {α : Type _} (l : List α) (i : Nat) : List α :=
  (l.take i) ++ (l.drop (i + 1))

/-- Evaluation of `removeAt` at index 0: drop the first element. -/
lemma removeAt_zero {α : Type} (l : List α) : removeAt l 0 = l.drop 1 := by
  simp [removeAt]

/-- `removeAt` is the identity when the index is at least the list length. -/
lemma removeAt_ge_length {α : Type} (l : List α) (i : Nat) (h : l.length ≤ i) : removeAt l i = l := by
  unfold removeAt
  have h_take : l.take i = l := List.take_of_length_le h
  have h_drop : l.drop (i + 1) = [] := by
    apply List.drop_eq_nil_of_le
    omega
  simp [h_take, h_drop]

/-- Remove a contiguous slice of a list from index `i` to `j` (inclusive).
`removeSlice l i j = l.take i ++ l.drop (j + 1)`. When `i = j`, this is equivalent to `removeAt l i`. -/
def removeSlice {α : Type} (l : List α) (i j : Nat) : List α :=
  (l.take i) ++ (l.drop (j + 1))

/-- `removeSlice` at a single index is the same as `removeAt`. -/
lemma removeSlice_eq_removeAt {α : Type} (l : List α) (i : Nat) : removeSlice l i i = removeAt l i := by
  simp [removeSlice, removeAt]

/-! ### `takenFromEnds` — take from both ends of a list -/

/-- Take `l` elements from the start and `r` elements from the end of a list.
For example, `takenFromEnds [a,b,c,d,e] 2 1 = [a,b] ++ [e] = [a,b,e]`. -/
def takenFromEnds {α : Type u} (xs : List α) (l r : Nat) : List α :=
  (xs.take l) ++ (xs.drop (xs.length - r))

/-- Replace the element at index `i` in list `as` with `a`.
If `i` is out of bounds (i.e., `i ≥ as.length`), returns `as` unchanged. -/
def listSet {α : Type u} (as : List α) (i : Nat) (a : α) : List α :=
  (as.take i) ++ [a] ++ (as.drop (i + 1))

/-- Set the element at index `i` in `xs` to `val`. If `i` is beyond the end
of the list, append `val` at the end. General-purpose list update utility. -/
def setOrAppend {α : Type} (xs : List α) (i : Nat) (val : α) : List α :=
  if i < xs.length then
    (xs.take i) ++ (val :: (xs.drop (i + 1)))
  else
    xs ++ [val]

lemma setOrAppend_eq_take_append_val_drop_of_lt {α : Type} (xs : List α) (i : Nat) (val : α) (h : i < xs.length) :
    setOrAppend xs i val = (xs.take i) ++ (val :: (xs.drop (i + 1))) := by
  unfold setOrAppend
  simp [h]

lemma setOrAppend_eq_append_of_not_lt {α : Type} (xs : List α) (i : Nat) (val : α) (h : ¬ i < xs.length) :
    setOrAppend xs i val = xs ++ [val] := by
  unfold setOrAppend
  simp [h]

/-! ### Modify element at a given index -/

/-- Apply a function to the element at a given index in a list.
If the index is out of bounds, the list is returned unchanged.
This generalizes `listSet`: `listSet as i a = modifyAtIndex (fun _ => a) as i`. -/
def modifyAtIndex {α : Type _} (f : α → α) : List α → Nat → List α
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, Nat.succ i => x :: modifyAtIndex f xs i

/-- Swap the elements at positions `i` and `j` of a list `l`.
If either index is out of bounds, the list is returned unchanged. -/
def swap {α : Type} (l : List α) (i j : Nat) : List α :=
  if h : i < l.length ∧ j < l.length then
    let a := l.get ⟨i, h.1⟩
    let b := l.get ⟨j, h.2⟩
    (l.set i b).set j a
  else
    l

/-! ### Properties of `List.set` -/

/-- Setting at index `i` and then getting at a different index `j ≠ i`
yields the same value as getting at `j` from the original list. -/
lemma get?_set_eq_of_ne {α : Type} (l : List α) (i j : Nat) (c : α) (hne : j ≠ i) :
    (l.set i c)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exfalso; exact hne rfl
      | succ j' => simp
    | succ i' =>
      cases j with
      | zero => simp
      | succ j' =>
        simp
        apply ih
        intro h; apply hne; simp [h]

/-- Setting at index `i` (which is within bounds) and then getting at `i`
returns the newly set value. -/
lemma get?_set_self {α : Type} (l : List α) (i : Nat) (c : α) (h : i < l.length) :
    (l.set i c)[i]? = some c := by
  induction l generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp
      apply ih
      simpa using h

/-! ### `get?` bounds lemmas -/

/-- If `l.length ≤ i`, then `l[i]? = none`. I.e., looking up an index past the end
of the list returns `none`. -/
lemma get?_eq_none_of_length_le {α : Type} (l : List α) (i : Nat) (h : l.length ≤ i) :
    l[i]? = none := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i
    · simp at h
    · rename_i n
      simp at h
      simp [ih n h]

/-- If `i < l.length`, then `l[i]? = some (l.get ⟨i, hi⟩)`. This is the in-bounds
counterpart to `get?_eq_none_of_length_le`. -/
lemma getElem?_eq_some_get {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l[i]? = some (l.get ⟨i, hi⟩) := by
  simp [hi]

/-- Indexing into a mapped list at a valid index retrieves the function
applied to the element at that index in the original list. -/
lemma map_getElem?_eq_some_get {α β : Type} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    (List.map f l)[i]? = some (f (l.get ⟨i, hi⟩)) := by
  simp [hi]

/-- `List.map` distributes over `!`-indexing:
`(l.map f)[i]! = f (l[i]!)` when `i` is in bounds.
This is the `get!` counterpart of `map_getElem?_eq_some_get`. -/
lemma map_get!_eq {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) : (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => exfalso; exact Nat.not_lt_zero _ h
  | cons a as ih =>
    match i with
    | 0 => simp
    | n+1 =>
      simp
      have hn_lt : n < as.length := by
        simpa [Nat.succ_lt_succ_iff] using h
      simpa using ih n hn_lt

/-- `List.map` commutes with `List.get!` for all indices when `f` fixes the default value.
Unlike `map_get!_eq`, this version does **not** require an in‑bounds hypothesis — the
out‑of‑bounds case is handled by the condition `f default = default`.
For example: `(l.map (λ a => a * k))[i]! = l[i]! * k` for `Int` with default `0`. -/
lemma map_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α)
    (h : f default = default) (i : Nat) : (List.map f l)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp [h]
  | cons a l ih =>
    simp only [List.map_cons]
    cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- Indexing into a mapped list with `getElem?` at a valid index returns
`some (f (l[i]!))`, using the `getElem!` notation.
This combines `map_getElem?_eq_some_get` with the `getElem!` convenience form. -/
lemma map_getElem?_eq_some_getElem! {α β : Type} [Inhabited α] (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) : (l.map f)[i]? = some (f (l[i]!)) := by
  have := map_getElem?_eq_some_get f l i h
  simpa [h] using this

/-- Insert `val` at position `pos` in `l`. Elements from index `pos` onward are shifted right.
If `pos ≥ l.length`, `val` is appended at the end.
This is the inverse of `removeAt`: `removeAt (insertAt l i x) i = l` when `i ≤ l.length`. -/
def insertAt {α : Type _} (l : List α) (pos : Nat) (val : α) : List α :=
  let (front, back) := l.splitAt pos
  front ++ (val :: back)

/-- `insertAt` increases the list length by exactly one. -/
lemma insertAt_length {α : Type _} (l : List α) (pos : Nat) (val : α) :
    (insertAt l pos val).length = l.length + 1 := by
  simp [insertAt, List.splitAt_eq, List.length_append, List.length_take, List.length_drop]
  omega


end List

namespace List

/-! ### Indexed element update -/

/-- Set the element at index `i` of list `as` to `val`.
If `i` is out of bounds (i.e., `i ≥ as.length`), the list is unchanged.
Uses `mapIdx` for indexed traversal; the index matches the position in the list
(0-indexed, from the head). -/
def setElem {α : Type} (as : List α) (i : Nat) (val : α) : List α :=
  as.mapIdx (fun idx a => if idx = i then val else a)

/-- `setElem` preserves the length of the list. -/
theorem setElem_length {α : Type} (as : List α) (i : Nat) (val : α) :
    (setElem as i val).length = as.length := by
  simp [setElem]

end List

namespace List

/-! ### Indexed increment (incAt) -/

/-- Increment the element at index `i` in a list by a given value.
    Generic over any type with addition.
    If `i` is out of bounds (≥ list length), returns the original list unchanged. -/
def incAt {α : Type} [Add α] : List α → Nat → α → List α
  | [], _, _ => []
  | (h :: t), 0, x => (h + x) :: t
  | (h :: t), Nat.succ i, x => h :: incAt t i x

/-- `incAt` preserves list length regardless of index and increment value. -/
lemma incAt_length {α : Type} [Add α] (l : List α) (i : Nat) (x : α) :
    (incAt l i x).length = l.length := by
  induction l generalizing i with
  | nil => simp [incAt]
  | cons h t ih =>
    cases i with
    | zero => simp [incAt]
    | succ i' => simp [incAt, ih i']

/-! ### `foldl` with projection via `min`/`max` over a `LinearOrder` -/

/-- `foldl` with `min` over the projection `f` starting from `init` is ≤ `init`.
Generalizes `foldl_min_cost_le_init` from `Nat` to any `LinearOrder`. -/
lemma foldl_min_proj_le_init {α β : Type} [LinearOrder β] (f : α → β) (l : List α) (init : β) :
    l.foldl (fun acc a => min acc (f a)) init ≤ init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h : min init (f x) ≤ init := min_le_left _ _
    exact le_trans (ih (min init (f x))) h

/-- If `x ∈ l`, then `foldl` with `min` over the projection `f` is ≤ `f x`.
Generalizes `foldl_min_cost_le_of_mem` from `Nat` to any `LinearOrder`. -/
lemma foldl_min_proj_le_of_mem {α β : Type} [LinearOrder β] (f : α → β) (l : List α) (init : β) (x : α) (hx : x ∈ l) :
    l.foldl (fun acc a => min acc (f a)) init ≤ f x := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    simp [List.mem_cons] at hx
    rcases hx with (heq | hx')
    · rw [heq]
      have h := foldl_min_proj_le_init f ys (min init (f y))
      exact le_trans h (min_le_right _ _)
    · exact ih (min init (f y)) hx'

/-- The result of folding `min` over a projection `f` is either `init` or equals `f x`
for some `x ∈ xs`. Generalizes `foldl_min_cost_eq_or` from `Nat` to any `LinearOrder`. -/
lemma foldl_min_proj_eq_or {α β : Type} [LinearOrder β] (f : α → β) (xs : List α) (init : β) :
    xs.foldl (fun acc x => min acc (f x)) init = init ∨
    ∃ x ∈ xs, xs.foldl (fun acc x => min acc (f x)) init = f x := by
  induction xs generalizing init with
  | nil => left; rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rcases ih (min init (f y)) with (h_eq | ⟨x, hx, h_eq⟩)
    · rw [h_eq]
      rcases min_choice init (f y) with (h_is_init | h_is_fy)
      · left; exact h_is_init
      · right; exact ⟨y, by simp, h_is_fy⟩
    · right; exact ⟨x, by simp [hx], h_eq⟩

/-- `init ≤ foldl` with `max` over the projection `f` starting from `init`.
This is the projection-based counterpart of `foldl_max_ge_init`. -/
lemma foldl_max_proj_ge_init {α β : Type} [LinearOrder β] (f : α → β) (l : List α) (init : β) :
    init ≤ l.foldl (fun acc a => max acc (f a)) init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h : init ≤ max init (f x) := le_max_left _ _
    exact le_trans h (ih (max init (f x)))

/-- If `x ∈ l`, then `f x ≤ foldl` with `max` over the projection `f`.
This is the projection-based counterpart of `foldl_max_ge_all`. -/
lemma foldl_max_proj_ge_of_mem {α β : Type} [LinearOrder β] (f : α → β) (l : List α) (init : β) (x : α) (hx : x ∈ l) :
    f x ≤ l.foldl (fun acc a => max acc (f a)) init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    simp [List.mem_cons] at hx
    rcases hx with (heq | hx')
    · rw [heq]
      have h : f y ≤ max init (f y) := le_max_right _ _
      have h_aux : max init (f y) ≤ ys.foldl (fun acc a => max acc (f a)) (max init (f y)) :=
        foldl_max_proj_ge_init f ys (max init (f y))
      exact le_trans h h_aux
    · exact ih (max init (f y)) hx'

end List

namespace List


/-! ### `replaceAt` — replace element at a given index -/

/-- Replace the element at index `i` in list `l` with value `v`.
If `i` is out of bounds (`i ≥ l.length`), the original list is returned unchanged. -/
def replaceAt {α : Type} (l : List α) (i : Nat) (v : α) : List α :=
  match l, i with
  | [], _ => []
  | _ :: xs, 0 => v :: xs
  | x :: xs, Nat.succ i' => x :: replaceAt xs i' v

/-- `replaceAt` preserves the length of the list. -/

lemma replaceAt_length {α : Type} (l : List α) (i : Nat) (v : α) :
    (replaceAt l i v).length = l.length := by
  induction l generalizing i with
  | nil => simp [replaceAt]
  | cons x xs ih =>
    cases i
    · simp [replaceAt]
    · simp [replaceAt, ih]

/-- After `replaceAt l i v`, getting the element at index `i` (assuming `i < l.length`)
returns `some v`. -/
lemma replaceAt_get?_eq {α : Type} (l : List α) (i : Nat) (v : α) (hi : i < l.length) :
    (replaceAt l i v)[i]? = some v := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [replaceAt]
    | succ i' =>
      simp [replaceAt]
      apply ih
      simpa using hi

/-- After `replaceAt l i v`, getting the element at a different index `j ≠ i` (assuming `j < l.length`)
returns the original element. -/
lemma replaceAt_get?_ne {α : Type} (l : List α) (i j : Nat) (v : α) (hne : j ≠ i) (hj : j < l.length) :
    (replaceAt l i v)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      cases i with
      | zero => exfalso; exact hne rfl
      | succ i' => simp [replaceAt]
    | succ j' =>
      cases i with
      | zero => simp [replaceAt]
      | succ i' =>
        simp [replaceAt]
        apply ih (i := i') (j := j')
        · intro h; apply hne; simpa [h]
        · simpa using hj

/-! ### `argminIdx` — index of the first minimum element -/

/-- Auxiliary for `argminIdx`: traverses `rest` starting from index `idx`,
maintaining the current minimum `curMin` and its index `curIdx`.
Returns the index of the first occurrence of the minimum element.
The strict comparison `y < curMin` ensures that the first (lowest index)
minimum is returned when multiple elements share the minimum value. -/
def argminIdxAux {α : Type} [LinearOrder α] (rest : List α) (idx curIdx : Nat) (curMin : α) :
    Nat :=
  match rest with
  | [] => curIdx
  | y :: ys =>
    if y < curMin then
      argminIdxAux ys (idx + 1) idx y
    else
      argminIdxAux ys (idx + 1) curIdx curMin

/-- Returns the index of the first minimum element in `l` (0-based).
For an empty list, returns `0`. -/
def argminIdx {α : Type} [LinearOrder α] (l : List α) : Nat :=
  match l with
  | [] => 0
  | x :: xs => argminIdxAux xs 1 0 x

/-! ### `insertAtAll` — insert element at all positions -/

/-- Insert element `a` at all possible positions in list `l`, returning
all resulting lists. The first result has `a` at the front, the last has `a` at the end.
`insertAtAll [x, y] a = [[a, x, y], [x, a, y], [x, y, a]]` -/
def insertAtAll {α : Type} : List α → α → List (List α)
  | [], a => [[a]]
  | y :: ys, a =>
    (a :: y :: ys) :: ((insertAtAll ys a).map fun l => y :: l)

/-- If `p ∈ insertAtAll q x`, then `p` is a permutation of `x :: q`. -/
theorem mem_insertAtAll_perm {α : Type} {x : α} {q p : List α} (h : p ∈ insertAtAll q x) :
    Perm p (x :: q) := by
  induction q generalizing p with
  | nil =>
    simp [insertAtAll] at h
    subst h
    exact Perm.refl _
  | cons y ys ih =>
    simp [insertAtAll] at h
    rcases h with (rfl | ⟨p', hp', rfl⟩)
    · exact Perm.refl _
    · have hp'_perm : Perm p' (x :: ys) := ih hp'
      have hcons : Perm (y :: p') (y :: x :: ys) := Perm.cons y hp'_perm
      have hswap : Perm (y :: x :: ys) (x :: y :: ys) := Perm.swap x y ys
      exact Perm.trans hcons hswap

/-- Length of `insertAtAll q x` equals `q.length + 1`. -/
theorem length_insertAtAll {α : Type} (x : α) (q : List α) : (insertAtAll q x).length = q.length + 1 := by
  induction q with
  | nil => simp [insertAtAll]
  | cons y ys ih =>
    simp [insertAtAll, ih, length_cons, length_map]

/-- If `x ∉ q` and `p ∈ insertAtAll q x`, then `p.erase x = q`. -/
theorem erase_of_mem_insertAtAll {α : Type} [DecidableEq α] {x : α} {q p : List α}
    (hxq : x ∉ q) (h : p ∈ insertAtAll q x) : p.erase x = q := by
  induction q generalizing p with
  | nil =>
    simp [insertAtAll] at h
    subst h
    simp
  | cons y ys ih =>
    have hx_ys : x ∉ ys := fun hx => hxq (mem_cons_of_mem _ hx)
    have hx_ne_y : x ≠ y := fun h_eq => hxq (h_eq ▸ mem_cons_self y ys)
    simp [insertAtAll] at h
    rcases h with (rfl | ⟨p', hp', rfl⟩)
    · simp [erase_cons_head]
    · rw [erase_cons_tail (by simpa [beq_iff_eq] using Ne.symm hx_ne_y), ih hx_ys hp']

/-- If `x ∉ q`, then `insertAtAll q x` has no duplicate entries. -/
theorem nodup_insertAtAll {α : Type} (x : α) (q : List α) (hxq : x ∉ q) : Nodup (insertAtAll q x) := by
  induction q with
  | nil =>
    simp [insertAtAll, nodup_singleton]
  | cons y ys ih =>
    have hx_ys : x ∉ ys := fun h => hxq (mem_cons_of_mem _ h)
    have hx_ne_y : x ≠ y := fun h => hxq (h ▸ mem_cons_self y ys)
    have hinj : Function.Injective (fun (l : List α) => y :: l) := by
      intro a b h
      injection h
    have h_nodup_map : Nodup ((insertAtAll ys x).map fun l => y :: l) :=
      Nodup.map hinj (ih hx_ys)
    have h_not_mem : x :: y :: ys ∉ ((insertAtAll ys x).map fun l => y :: l) := by
      intro hmem
      rcases (List.mem_map (f := fun (l : List α) => y :: l)).mp hmem with ⟨p', hp', h_eq⟩
      have h_eq' : y :: p' = x :: y :: ys := h_eq
      injection h_eq' with h_eq_head _
      exact hx_ne_y h_eq_head.symm
    simpa [insertAtAll] using (Nodup.cons h_not_mem h_nodup_map)

/-- Disjointness: if `x ∉ q₁` and `x ∉ q₂` and `q₁ ≠ q₂`, then
`insertAtAll q₁ x` and `insertAtAll q₂ x` have no common elements. -/
theorem disjoint_insertAtAll {α : Type} [DecidableEq α] {x : α} {q₁ q₂ : List α}
    (hxq₁ : x ∉ q₁) (hxq₂ : x ∉ q₂) (hne : q₁ ≠ q₂) :
    Disjoint (insertAtAll q₁ x) (insertAtAll q₂ x) := by
  intro p hp₁ hp₂
  apply hne
  have h_eq₁ : p.erase x = q₁ := erase_of_mem_insertAtAll hxq₁ hp₁
  have h_eq₂ : p.erase x = q₂ := erase_of_mem_insertAtAll hxq₂ hp₂
  rw [h_eq₁] at h_eq₂
  exact h_eq₂

/-! ### `allPerms` — generate all permutations by recursive insertion -/

/-- Generate all permutations of a list by recursively inserting each element
at all positions in the permutations of the rest. -/
def allPerms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let permsRest := allPerms xs
    permsRest.flatMap (fun q => insertAtAll q x)

/-- Every result of `allPerms l` is a permutation of `l`. -/
theorem perm_of_mem_allPerms {α : Type} {l p : List α} (h : p ∈ allPerms l) : Perm p l := by
  induction l generalizing p with
  | nil =>
    simp [allPerms] at h
    subst h
    exact Perm.nil
  | cons x xs ih =>
    have h' : p ∈ ((allPerms xs).flatMap (fun q => insertAtAll q x)) := by
      simpa [allPerms] using h
    rw [mem_flatMap] at h'
    rcases h' with ⟨q, hq, hp⟩
    have hq_perm : Perm q xs := ih hq
    have hp_perm : Perm p (x :: q) := mem_insertAtAll_perm hp
    have hcons : Perm (x :: q) (x :: xs) := Perm.cons x hq_perm
    exact Perm.trans hp_perm hcons

/-- If the input list has no duplicates, then `allPerms l` produces a list with no duplicates. -/
theorem nodup_allPerms {α : Type} [DecidableEq α] {l : List α} (h_nodup : Nodup l) :
    Nodup (allPerms l) := by
  induction l with
  | nil =>
    simp [allPerms]
  | cons x xs ih =>
    have hx_xs : x ∉ xs := (nodup_cons.mp h_nodup).left
    have hxs_nodup : Nodup xs := (nodup_cons.mp h_nodup).right
    simp [allPerms]
    rw [nodup_flatMap]
    constructor
    · intro q hq
      have hxq : x ∉ q := by
        have hq_perm : Perm q xs := perm_of_mem_allPerms hq
        intro hxq'
        exact hx_xs ((hq_perm.mem_iff).mp hxq')
      exact nodup_insertAtAll x q hxq
    · have h_all_nodup : Nodup (allPerms xs) := ih hxs_nodup
      refine h_all_nodup.pairwise_of_forall_ne ?_
      intro q₁ hq₁ q₂ hq₂ hne
      have hxq₁ : x ∉ q₁ := by
        have hq_perm : Perm q₁ xs := perm_of_mem_allPerms hq₁
        intro hxq'; exact hx_xs ((hq_perm.mem_iff).mp hxq')
      have hxq₂ : x ∉ q₂ := by
        have hq_perm : Perm q₂ xs := perm_of_mem_allPerms hq₂
        intro hxq'; exact hx_xs ((hq_perm.mem_iff).mp hxq')
      exact disjoint_insertAtAll hxq₁ hxq₂ hne

/-- Completeness of `insertAtAll`: the list formed by inserting `x` after prefix `s`
and before suffix `t` is always a member of `insertAtAll (s ++ t) x`. -/
lemma mem_insertAtAll_of_split {α : Type} (x : α) (s t : List α) :
    s ++ x :: t ∈ insertAtAll (s ++ t) x := by
  induction s with
  | nil =>
    cases t with
    | nil => simp [insertAtAll]
    | cons y ys => simp [insertAtAll]
  | cons a s' ih =>
    simp only [List.cons_append, insertAtAll]
    apply mem_cons_of_mem
    apply mem_map.mpr
    exact ⟨s' ++ x :: t, ih, rfl⟩

/-- Perm removal lemma: if `s ++ x :: t` is a permutation of `x :: xs`,
then `s ++ t` is a permutation of `xs`. -/
lemma perm_remove_mid {α : Type} [DecidableEq α] (x : α) (s t xs : List α)
    (hperm : Perm (s ++ x :: t) (x :: xs)) : Perm (s ++ t) xs := by
  rw [List.perm_iff_count] at hperm ⊢
  intro a
  have h := hperm a
  simp [List.count_append] at h ⊢
  by_cases hax : a = x
  · subst hax; simp at h ⊢; omega
  · simp [hax] at h ⊢; exact h

/-- If `x ∈ l`, then there exist `s` and `t` such that `l = s ++ x :: t`. -/
lemma exists_append_of_mem {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∃ s t, l = s ++ x :: t := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp at h
    rcases h with (rfl | hm)
    · exact ⟨[], ys, rfl⟩
    · rcases ih hm with ⟨s, t, h⟩
      exact ⟨y :: s, t, by simp [h]⟩

/-- Completeness of `allPerms`: if `p` is a permutation of `l`, then `p` is in `allPerms l`.
Together with `perm_of_mem_allPerms`, this gives `p ∈ allPerms l ↔ Perm p l`. -/
theorem mem_allPerms_of_perm {α : Type} [DecidableEq α] {l p : List α} (h : Perm p l) :
    p ∈ allPerms l := by
  induction l generalizing p with
  | nil =>
    have hp_nil : p = [] := Perm.eq_nil h
    subst hp_nil
    simp [allPerms]
  | cons x xs ih =>
    have hx_mem : x ∈ p := (h.mem_iff (a := x)).mpr (by simp)
    rcases exists_append_of_mem hx_mem with ⟨s, t, hsplit⟩
    rw [hsplit]
    have hrest : Perm (s ++ t) xs :=
      perm_remove_mid x s t xs (hsplit ▸ h)
    have hrest_perms : s ++ t ∈ allPerms xs := ih hrest
    simp [allPerms]
    exact ⟨s ++ t, hrest_perms, mem_insertAtAll_of_split x s t⟩

/-- `allPerms` is sound and complete: `p ∈ allPerms l ↔ Perm p l`. -/
theorem allPerms_iff_perm {α : Type} [DecidableEq α] (l p : List α) :
    p ∈ allPerms l ↔ Perm p l :=
  ⟨perm_of_mem_allPerms, mem_allPerms_of_perm⟩

/-! ### `nodup_map_permutations` — mapping an injective function over permutations preserves nodup -/

/-- If `f` is injective and `l` has no duplicates, then mapping `f` over `List.permutations l`
yields a list with no duplicates. This combines `List.nodup_permutations` with `List.Nodup.map`. -/
lemma nodup_map_permutations {α β : Type} {f : List α → β} (hf : Function.Injective f)
    {l : List α} (h : l.Nodup) : ((List.permutations l).map f).Nodup :=
  List.Nodup.map hf (List.nodup_permutations l h)


end List
