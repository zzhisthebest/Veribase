import general.List.IndexedAccess
import general.List.IndexedUpdate
import general.List.Transformations
import general.List.Sequences

namespace List

private lemma foldMin_le_initial {α : Type} [LinearOrder α] (xs : List α) (a : α) :
    xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left _ _)

private lemma foldMin_le_member {α : Type} [LinearOrder α] (xs : List α) (a x : α)
    (h : x ∈ xs) : xs.foldl min a ≤ x := by
  induction xs generalizing a with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact (foldMin_le_initial ys (min a x)).trans (min_le_right _ _)
    · exact ih (min a y) h

/-! ### `maxOn` — maximum of `f x` over `x ∈ l` -/

/-- `maxOn f xs` computes the maximum value of `f x` over all `x ∈ xs`.
Returns `0` for the empty list (the identity of `Nat.max`). -/
def maxOn {α : Type _} (f : α → Nat) (xs : List α) : Nat :=
  (xs.map f).foldl Nat.max 0

lemma maxOn_nil {α : Type _} (f : α → Nat) : maxOn f [] = 0 := rfl

/-- `maxOver f xs` computes the maximum value of `f x` over all `x ∈ xs`.
Returns `0` for the empty list. This is a structurally recursive version of `maxOn`. -/
def maxOver {α : Type u} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: rest => max (f x) (maxOver f rest)

private lemma foldl_max_eq_max_foldl' (xs : List Nat) (a : Nat) :
    xs.foldl max a = max a (xs.foldl max 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons]
    rw [ih (max a x), ih x, max_assoc]

/-- `maxOver` and `maxOn` are equivalent. -/
lemma maxOver_eq_maxOn {α : Type _} (f : α → Nat) (xs : List α) : maxOver f xs = maxOn f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [maxOver, maxOn]
    rw [foldl_max_eq_max_foldl' (map f xs) (f x)]
    rw [ih]
    rfl

/-! ### `minimumOn` — minimum of `f x` over `x ∈ l`, returning `Option` -/

/-- `minimumOn f xs` computes the minimum value of `f x` over all `x ∈ xs`.
Returns `none` for the empty list. Generalizes `maxOn` (which returns `0` for empty)
by using `Option` to correctly handle the empty case, and works for any type `β`
with a `Min` instance (not just `Nat`).

`listMinimumOn` was the original name in problem sources. -/
def minimumOn {α β : Type} [Min β] (f : α → β) (as : List α) : Option β :=
  as.foldl (fun opt a =>
    match opt with
    | none => some (f a)
    | some b => some (min b (f a))) none


theorem minimumOn_nil {α β : Type} [Min β] (f : α → β) : minimumOn f [] = none := by
  simp [minimumOn]


theorem minimumOn_singleton {α β : Type} [Min β] (f : α → β) (x : α) :
    minimumOn f [x] = some (f x) := by
  simp [minimumOn]

/-- `minimumOn` returns `none` iff the input list is empty. -/
theorem minimumOn_eq_none_iff {α β : Type} [Min β] (f : α → β) (as : List α) :
    minimumOn f as = none ↔ as = [] := by
  let step : Option β → α → Option β := fun opt a =>
    match opt with
    | none => some (f a)
    | some b => some (min b (f a))
  have aux (l : List α) (b : β) : l.foldl step (some b) ≠ none := by
    induction l generalizing b with
    | nil => simp
    | cons x xs ih => exact ih (min b (f x))
  cases as with
  | nil => simp [minimumOn]
  | cons x xs =>
    have h := aux xs (f x)
    simpa [minimumOn, step] using h

/-! ### `removeMin` — extract the minimum element from a list, returning both the element and the remaining list -/

/-- Returns the minimum element of a list (according to `≤`) paired with the list
obtained by removing the first occurrence of that minimum element.
For an empty list, returns `(default, [])`. -/
def removeMin [LinearOrder α] [Inhabited α] (l : List α) : α × List α :=
  match l with
  | [] => (default, [])
  | [x] => (x, [])
  | x :: xs =>
    let (m, rest) := removeMin xs
    if x ≤ m then (x, xs) else (m, x :: rest)

/-- In a non-empty list, the first component of `removeMin` is a member of the list. -/
lemma removeMin_fst_mem [LinearOrder α] [Inhabited α] {l : List α} (hne : l ≠ []) :
    (removeMin l).1 ∈ l := by
  induction' l with x xs ih
  · exact absurd rfl hne
  · cases xs with
    | nil => simp [removeMin]
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have ih' := ih hne'
      have hcalc : removeMin (x :: y :: ys) =
          (let (m, rest) := removeMin (y :: ys)
           if x ≤ m then (x, y :: ys) else (m, x :: rest)) := rfl
      rw [hcalc]
      dsimp
      split
      · simp
      · simp [ih']

/-- In a non-empty list, the first component of `removeMin` is ≤ every element. -/
lemma removeMin_fst_le_all [LinearOrder α] [Inhabited α] {l : List α} (hne : l ≠ []) :
    ∀ a ∈ l, (removeMin l).1 ≤ a := by
  induction' l with x xs ih
  · exact absurd rfl hne
  · cases xs with
    | nil =>
      intro a ha
      simp at ha
      subst ha
      simp [removeMin]
    | cons y ys =>
      have hne' : y :: ys ≠ [] := by simp
      have ih' := ih hne'
      have hcalc : removeMin (x :: y :: ys) =
          (let (m, rest) := removeMin (y :: ys)
           if x ≤ m then (x, y :: ys) else (m, x :: rest)) := rfl
      rw [hcalc]
      dsimp
      intro b hb
      have hb_cases : b = x ∨ b ∈ y :: ys := by simpa using hb
      rcases hb_cases with (h_eq | hb')
      · rw [h_eq]
        by_cases h_cond : x ≤ (removeMin (y :: ys)).1
        · simp [h_cond]
        · simp [h_cond]
          exact le_of_lt (lt_of_not_ge h_cond)
      · have ih_b : (removeMin (y :: ys)).1 ≤ b := ih' b hb'
        by_cases h_cond : x ≤ (removeMin (y :: ys)).1
        · simp [h_cond]
          exact le_trans h_cond ih_b
        · simp [h_cond]
          exact ih_b

/-- If the input list has at most one element, `removeMin` returns an empty remainder. -/
lemma removeMin_rest_empty_of_length_le_one [LinearOrder α] [Inhabited α] {xs : List α}
    (h : xs.length ≤ 1) : (removeMin xs).2 = [] := by
  match xs with
  | [] => rfl
  | [x] => rfl

/-! ### `argminOfCons` — find the element minimizing a cost function `f : α → Nat` -/

/-- A single step of foldl that keeps the element with the minimal `f`-value.
If `f x` is less than the current best value `acc.2`, replace the accumulator
with `(x, f x)`; otherwise keep the current accumulator. -/
def argminFoldStepOfCons {α : Type} (f : α → Nat) (acc : α × Nat) (x : α) : α × Nat :=
  let v := f x
  if v < acc.2 then (x, v) else acc

/-- Find the element in `a :: l` that minimizes `f : α → Nat`.
Uses a left fold over `l` starting from `(a, f a)`, keeping the best candidate.
Returns `a` when `l` is empty (the only element minimizes `f` trivially).
Contrast with `List.argmin` (from Std) which returns `Option α` for the empty list case,
and `minCost` which returns the minimum cost value itself. `argminOfCons` returns
the element achieving that minimum cost in a known-nonempty list. -/
def argminOfCons {α : Type} (f : α → Nat) (l : List α) (a : α) : α :=
  (l.foldl (argminFoldStepOfCons f) (a, f a)).1

/-- If `x ∈ a :: l`, then `x ∈ a :: b :: l` for any `b`. -/
lemma mem_cons_cons {α : Type} {x a b : α} {l : List α} (h : x ∈ a :: l) : x ∈ a :: b :: l := by
  cases h
  · exact .head _
  · exact .tail _ (.tail _ ‹_›)

/-- `argminOfCons f l a` is in `a :: l`, and its `f`-value is minimal among all elements of `a :: l`. -/
lemma argminOfCons_mem_and_minimal {α : Type} (f : α → Nat) (l : List α) (a : α) :
    argminOfCons f l a ∈ a :: l ∧
    (∀ x ∈ a :: l, f (argminOfCons f l a) ≤ f x) := by
  unfold argminOfCons argminFoldStepOfCons
  induction' l with y ys ih generalizing a
  · simp
  · have h_foldl : (y :: ys).foldl (fun (acc : α × Nat) (x : α) =>
      let v := f x
      if v < acc.2 then (x, v) else acc
    ) (a, f a) = ys.foldl (fun (acc : α × Nat) (x : α) =>
      let v := f x
      if v < acc.2 then (x, v) else acc
    ) (if f y < f a then (y, f y) else (a, f a)) := by
      simp
    rw [h_foldl]
    by_cases h : f y < f a
    · have h_cond : (if f y < f a then (y, f y) else (a, f a)) = (y, f y) := by simp [h]
      rw [h_cond]
      have ih' := ih y
      rcases ih' with ⟨hmem, hmin⟩
      constructor
      · exact List.mem_cons_of_mem a hmem
      · intro x hx
        cases hx with
        | head _ =>
          have hfy : f (ys.foldl (fun (acc : α × Nat) (x : α) =>
              let v := f x
              if v < acc.2 then (x, v) else acc
            ) (y, f y)).1 ≤ f y := hmin y (by simp)
          exact Nat.le_of_lt (Nat.lt_of_le_of_lt hfy h)
        | tail _ hx' =>
          cases hx' with
          | head _ => exact hmin y (by simp)
          | tail _ hx_ys => exact hmin x (List.mem_cons_of_mem y hx_ys)
    · have h_cond : (if f y < f a then (y, f y) else (a, f a)) = (a, f a) := by simp [h]
      rw [h_cond]
      have ih' := ih a
      rcases ih' with ⟨hmem, hmin⟩
      constructor
      · exact mem_cons_cons hmem
      · intro x hx
        cases hx with
        | head _ => exact hmin a (by simp)
        | tail _ hx' =>
          cases hx' with
          | head _ =>
            have ha : f (ys.foldl (fun (acc : α × Nat) (x : α) =>
                let v := f x
                if v < acc.2 then (x, v) else acc
              ) (a, f a)).1 ≤ f a := hmin a (by simp)
            have hle : f a ≤ f y := Nat.ge_of_not_lt h
            exact Nat.le_trans ha hle
          | tail _ hx_ys => exact hmin x (List.mem_cons_of_mem a hx_ys)

/-- If `x ∈ xs`, then `f x ≤ maxOver f xs`. -/
lemma maxOver_ge {α : Type u} (f : α → Nat) (xs : List α) (x : α)
    (h : x ∈ xs) : f x ≤ maxOver f xs := by
  induction' xs with c cs ih generalizing x
  · exact absurd h (List.not_mem_nil _)
  · simp at h
    rcases h with (rfl | h')
    · rw [maxOver]; apply Nat.le_max_left
    · rw [maxOver]
      have hle := ih x h'
      apply Nat.le_trans hle
      apply Nat.le_max_right

/-- If `xs ≠ []`, then there exists `x ∈ xs` such that `f x = maxOver f xs`. -/
lemma maxOver_achieved {α : Type u} (f : α → Nat) (xs : List α)
    (hne : xs ≠ []) : ∃ x, x ∈ xs ∧ f x = maxOver f xs := by
  induction' xs with c cs ih
  · contradiction
  · by_cases hcs_empty : cs = []
    · use c
      have : maxOver f (c :: cs) = f c := by
        simp [maxOver, hcs_empty]
      simp [this]
    · rcases ih hcs_empty with ⟨x, hx, heq⟩
      by_cases hle : maxOver f cs ≤ f c
      · use c
        have hmax : maxOver f (c :: cs) = f c := by
          simp [maxOver, Nat.max_eq_left hle, heq]
        simp [hmax]
      · use x
        have hlt : f c < maxOver f cs := Nat.lt_of_not_ge hle
        have hmax : maxOver f (c :: cs) = maxOver f cs := by
          simp [maxOver, Nat.max_eq_right (Nat.le_of_lt hlt), heq]
        simp [hmax, heq, List.mem_cons_of_mem _ hx]

/-! ### `maxOverPairs` — maximum of a binary function over two lists -/

/-- Compute the maximum value of `f x y` over all `x ∈ xs` and `y ∈ ys`.
Returns `0` when either list is empty.
This is the maximum of `f` over the cartesian product `xs × ys`. -/
def maxOverPairs {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) : Nat :=
  xs.foldl (fun acc x =>
    ys.foldl (fun acc' y =>
      let s := f x y
      if s > acc' then s else acc')
    acc)
  0


lemma maxOverPairs_nil_left {α β : Type} (ys : List β) (f : α → β → Nat) :
    maxOverPairs ([] : List α) ys f = 0 := rfl


lemma maxOverPairs_nil_right {α β : Type} (xs : List α) (f : α → β → Nat) :
    maxOverPairs xs ([] : List β) f = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [maxOverPairs, ih]

/-- `maxOverPairs` reduces to `maxOn (f x) ys` when `xs = [x]`. -/
lemma maxOverPairs_singleton_left {α β : Type} (x : α) (ys : List β) (f : α → β → Nat) :
    maxOverPairs [x] ys f = maxOn (f x) ys := by
  calc
    maxOverPairs [x] ys f
        = ys.foldl (fun acc' y => if f x y > acc' then f x y else acc') 0 := rfl
    _ = ys.foldl (fun acc' y => max acc' (f x y)) 0 := by
      refine congrArg (fun g => ys.foldl g 0) (funext fun acc' => funext fun y => ?_)
      by_cases h : f x y > acc'
      · simp [h, Nat.max_eq_right (Nat.le_of_lt h)]
      · simp [h, Nat.max_eq_left (Nat.le_of_not_gt h)]
    _ = (ys.map (f x)).foldl max 0 := by rw [List.foldl_map]
    _ = maxOn (f x) ys := rfl

/-- `maxOverPairs` reduces to `maxOn (fun x => f x y) xs` when `ys = [y]`. -/
lemma maxOverPairs_singleton_right {α β : Type} (xs : List α) (y : β) (f : α → β → Nat) :
    maxOverPairs xs [y] f = maxOn (fun x => f x y) xs := by
  calc
    maxOverPairs xs [y] f
        = xs.foldl (fun acc x =>
            [y].foldl (fun acc' y' => if f x y' > acc' then f x y' else acc') acc
          ) 0 := rfl
    _ = xs.foldl (fun acc x => if f x y > acc then f x y else acc) 0 := by simp
    _ = xs.foldl (fun acc x => max acc (f x y)) 0 := by
      refine congrArg (fun g => xs.foldl g 0) (funext fun acc => funext fun x => ?_)
      by_cases h : f x y > acc
      · simp [h, Nat.max_eq_right (Nat.le_of_lt h)]
      · simp [h, Nat.max_eq_left (Nat.le_of_not_gt h)]
    _ = (xs.map (fun x => f x y)).foldl max 0 := by rw [List.foldl_map]
    _ = maxOn (fun x => f x y) xs := rfl

private lemma maxOverPairs_as_maxOver {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    maxOverPairs xs ys f = maxOver (fun x => maxOver (f x) ys) xs := by
  have inner (l : List β) (x : α) (a : Nat) :
      l.foldl (fun b y => if f x y > b then f x y else b) a = max a (maxOver (f x) l) := by
    induction l generalizing a with
    | nil => simp [maxOver]
    | cons y ys ih =>
      simp only [List.foldl_cons, maxOver, ih]
      by_cases h : f x y > a
      · simp [h, max_eq_right (le_of_lt h), ← max_assoc]
      · simp [h, max_eq_left (Nat.le_of_not_gt h), ← max_assoc]
  have outer (l : List α) (a : Nat) :
      l.foldl (fun b x => max b (maxOver (f x) ys)) a = max a (maxOver (fun x => maxOver (f x) ys) l) := by
    induction l generalizing a with
    | nil => simp [maxOver]
    | cons x xs ih => simp [List.foldl_cons, maxOver, ih, max_assoc]
  unfold maxOverPairs
  simp only [inner]
  simpa using outer xs 0

/-- If `x ∈ xs` and `y ∈ ys`, then `f x y ≤ maxOverPairs xs ys f`. -/
lemma maxOverPairs_ge {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat)
    {x : α} {y : β} (hx : x ∈ xs) (hy : y ∈ ys) : f x y ≤ maxOverPairs xs ys f := by
  rw [maxOverPairs_as_maxOver]
  exact (maxOver_ge (f x) ys y hy).trans (maxOver_ge (fun x => maxOver (f x) ys) xs x hx)

/-- If both `xs` and `ys` are nonempty, then there exist `x ∈ xs` and `y ∈ ys`
such that `f x y = maxOverPairs xs ys f`. In other words,
the maximum value is always attained by some pair. -/
lemma maxOverPairs_achieved {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat)
    (hxs : xs ≠ []) (hys : ys ≠ []) : ∃ x, x ∈ xs ∧ ∃ y, y ∈ ys ∧ f x y = maxOverPairs xs ys f := by
  rw [maxOverPairs_as_maxOver]
  obtain ⟨x, hx, he⟩ := maxOver_achieved (fun x => maxOver (f x) ys) xs hxs
  obtain ⟨y, hy, he'⟩ := maxOver_achieved (f x) ys hys
  exact ⟨x, hx, y, hy, he'.trans he⟩

/-- `maxOverPairs` is equivalent to computing `maxOn` on `xs` of `maxOn (f x) ys`. -/
lemma maxOverPairs_eq_maxOn {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    maxOverPairs xs ys f = maxOn (fun x => maxOn (f x) ys) xs := by
  simp only [maxOverPairs_as_maxOver, maxOver_eq_maxOn]

/-! ### `maxOf` — maximum of a `List Nat` (returns `0` for empty) -/

/-- Maximum of a `List Nat`; `0` for the empty list.
Equivalent to `maxOver id`, `maxOn id`, and `List.foldr max 0`. -/
def maxOf : List Nat → Nat := maxOver id


lemma maxOf_nil : maxOf [] = 0 := rfl


lemma maxOf_cons (y : Nat) (ys : List Nat) : maxOf (y :: ys) = max y (maxOf ys) := rfl


lemma maxOf_singleton (x : Nat) : maxOf [x] = x := by
  simp [maxOf, maxOver]

/-- Every element of `xs` is ≤ `maxOf xs`. -/
lemma maxOf_ge_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ maxOf xs :=
  maxOver_ge id xs x h

/-- If a nonempty list has all elements ≥ 1, then its maximum is also ≥ 1. -/
lemma maxOf_pos_of_nonempty (xs : List Nat) (h_nonempty : xs ≠ []) (h_one : ∀ x ∈ xs, 1 ≤ x) :
    1 ≤ maxOf xs := by
  have hlen : 0 < xs.length := List.length_pos.mpr h_nonempty
  rcases List.exists_mem_of_length_pos hlen with ⟨x, hx⟩
  have hx_one := h_one x hx
  have hx_le_max := maxOf_ge_mem hx
  exact le_trans hx_one hx_le_max

/-- `maxOf` is equivalent to `List.foldr max 0`. -/
lemma maxOf_eq_foldr_max : maxOf = List.foldr max 0 := by
  funext l
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [maxOf_cons, List.foldr, ih]

/-- For any `f : α → Nat` and `x ∈ l`, `f x ≤ maxOf (l.map f)`. -/
lemma maxOf_ge_of_mem_map {α : Type u} (f : α → Nat) (l : List α) {x : α} (hx : x ∈ l) :
    f x ≤ maxOf (l.map f) :=
  maxOver_ge id (l.map f) (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-! ### `minOf` — minimum of a `List Nat` (returns `0` for empty) -/

/-- Minimum of a `List Nat`; `0` for the empty list.
On a nonempty list, folds `Nat.min` starting from the head element.
Analogous to `maxOf`. -/
def minOf (l : List Nat) : Nat :=
  match l with
  | []      => 0
  | h :: t  => List.foldl Nat.min h t


lemma minOf_nil : minOf [] = 0 := rfl

lemma minOf_cons (y : Nat) (ys : List Nat) : minOf (y :: ys) = List.foldl Nat.min y ys := rfl


lemma minOf_singleton (x : Nat) : minOf [x] = x := by
  simp [minOf]

/-- The minimum of a list is at most each of its elements. -/
lemma minOf_le_of_mem (x : Nat) (xs : List Nat) (h : x ∈ xs) : minOf xs ≤ x := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldMin_le_initial xs x
    · exact foldMin_le_member xs a x h

/-- For any `f : α → Nat` and `x ∈ l`, `minOf (l.map f) ≤ f x`. -/
lemma minOf_le_of_mem_map {α : Type u} (f : α → Nat) (l : List α) {x : α} (hx : x ∈ l) :
    minOf (l.map f) ≤ f x := by
  have hmem : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
  exact minOf_le_of_mem (f x) (l.map f) hmem

/-! ### Top two elements -/

/-- A single fold-step that tracks the two largest values seen so far.
Given a new element `d` and the current `(largest, secondLargest)` pair
`(m1, m2)`, returns the updated pair. -/
def topTwoStep (d m1 m2 : Nat) : Nat × Nat :=
  if d > m1 then (d, m1)
  else if d > m2 then (m1, d)
  else (m1, m2)

/-- Compute the two largest elements in a list of natural numbers.
Returns `(largest, secondLargest)`. Missing slots (for lists with fewer
than two elements) are filled with `0`. -/
def topTwo (xs : List Nat) : Nat × Nat :=
  xs.foldl (fun p d => topTwoStep d p.1 p.2) (0, 0)

/-- The top-two fold step preserves the invariant that the second element is
not greater than the first. -/
lemma topTwoStep_preserves_le (d m1 m2 : Nat) (h : m2 ≤ m1) :
    (topTwoStep d m1 m2).2 ≤ (topTwoStep d m1 m2).1 := by
  unfold topTwoStep
  by_cases h_gt : d > m1
  · simp [h_gt]
    exact Nat.le_of_lt h_gt
  · simp [h_gt]
    by_cases h_gt2 : d > m2
    · simp [h_gt2]
      exact Nat.le_of_not_gt h_gt
    · simp [h_gt2]
      exact h

/-- The invariant `snd ≤ fst` is preserved throughout the `topTwo` fold. -/
lemma topTwo_foldl_invariant (xs : List Nat) (acc : Nat × Nat) (h : acc.2 ≤ acc.1) :
    (xs.foldl (fun p d => topTwoStep d p.1 p.2) acc).2 ≤
    (xs.foldl (fun p d => topTwoStep d p.1 p.2) acc).1 := by
  induction' xs with x xs ih generalizing acc
  · exact h
  · have hstep : (topTwoStep x acc.1 acc.2).2 ≤ (topTwoStep x acc.1 acc.2).1 :=
      topTwoStep_preserves_le x acc.1 acc.2 h
    have h_next := ih (topTwoStep x acc.1 acc.2) hstep
    exact h_next

/-- The second element of `topTwo` is never greater than the first. -/
lemma topTwo_snd_le_fst (xs : List Nat) : (topTwo xs).2 ≤ (topTwo xs).1 := by
  unfold topTwo
  apply topTwo_foldl_invariant xs (0, 0)
  decide

/-- Find the second-largest *distinct* natural number in a list.
Returns `none` if the list contains fewer than two distinct values. -/
def secondLargestDistinctNat (xs : List Nat) : Option Nat :=
  let uniq := xs.eraseDup
  if uniq.length ≤ 1 then
    none
  else
    some (topTwo uniq).2

/-- Find the second-largest distinct element in a list over any `LinearOrder`.
Returns `none` if the list contains fewer than two distinct values.
Uses `List.maximum` to find the top two elements. -/
def secondLargestDistinct {α : Type} [LinearOrder α] (xs : List α) : Option α :=
  let distinct := xs.eraseDup
  match distinct.maximum with
  | ⊥ => none
  | (maxVal : α) =>
    let rest := distinct.filter (fun x => x != maxVal)
    match rest.maximum with
    | ⊥ => none
    | (r : α) => some r

/-- When `m` is the maximum of `l` and `r` is the maximum of elements in `l` not equal to `m`,
then `m` and `r` are the two largest distinct elements of `l`. -/
lemma maximum_filter_ne_properties {α : Type} [LinearOrder α] {l : List α} {m r : α}
    (hmax : l.maximum = (m : WithBot α))
    (hrest : (l.filter (fun x => x ≠ m)).maximum = (r : WithBot α)) :
    m ∈ l ∧ r ∈ l ∧ m ≠ r ∧ r < m ∧ (∀ z ∈ l, z ≤ m) ∧ (∀ z ∈ l, z ≠ m → z ≤ r) := by
  have hmax_mem : m ∈ l := (List.maximum_eq_coe_iff.mp hmax).left
  have hmax_le : ∀ z ∈ l, z ≤ m := (List.maximum_eq_coe_iff.mp hmax).right
  have hr_mem_filter : r ∈ l.filter (fun x => x ≠ m) :=
    (List.maximum_eq_coe_iff.mp hrest).left
  have hr_mem : r ∈ l := (List.mem_filter.mp hr_mem_filter).left
  have hr_ne_m : r ≠ m := by
    have := (List.mem_filter.mp hr_mem_filter).right
    simpa using this
  have hr_le_filter : ∀ z ∈ l.filter (fun x => x ≠ m), z ≤ r :=
    (List.maximum_eq_coe_iff.mp hrest).right
  have hr_lt_m : r < m := by
    have hle : r ≤ m := hmax_le r hr_mem
    exact lt_of_le_of_ne hle hr_ne_m
  have hall_rest : ∀ z ∈ l, z ≠ m → z ≤ r := by
    intro z hz hzne
    have hz_mem_filter : z ∈ l.filter (fun x => x ≠ m) := by
      rw [List.mem_filter]
      exact ⟨hz, by simpa using hzne⟩
    exact hr_le_filter z hz_mem_filter
  exact ⟨hmax_mem, hr_mem, hr_ne_m.symm, hr_lt_m, hmax_le, hall_rest⟩

/-! ### `foldlMaxBy` — maximum of a mapped function over filtered elements -/

/-- Fold a list, taking the maximum of `f x` for elements `x` satisfying `p`,
starting from initial value `init`. This generalizes `maxMeasureWhere`
(which always uses `init = 0`) by allowing an arbitrary initial accumulator. -/
def foldlMaxBy {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) (init : Nat) : Nat :=
  l.foldl (fun best x => if p x then Nat.max best (f x) else best) init

/-- The result of `foldlMaxBy` is at least the initial value. -/
lemma foldlMaxBy_ge {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) (init : Nat) :
    init ≤ foldlMaxBy l p f init := by
  induction' l with x xs ih generalizing init
  · simp [foldlMaxBy]
  · simp [foldlMaxBy, List.foldl]
    by_cases hx : p x
    · simp [hx]
      have hle : init ≤ Nat.max init (f x) := Nat.le_max_left _ _
      exact Nat.le_trans hle (ih (Nat.max init (f x)))
    · simp [hx]
      exact ih init

/-- If the result of `foldlMaxBy` strictly exceeds the initial value,
then there exists an element in the list satisfying the predicate `p`
and whose `f`-value equals the result. -/
lemma foldlMaxBy_mem {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) (init m : Nat)
    (h_fold : foldlMaxBy l p f init = m) (h_lt : init < m) : ∃ x ∈ l, p x ∧ f x = m := by
  unfold foldlMaxBy at h_fold
  induction' l with x xs ih generalizing init m
  · simp at h_fold; linarith
  · simp [List.foldl] at h_fold
    by_cases hx : p x
    · simp [hx] at h_fold
      by_cases hle : f x ≤ init
      · have hmax_eq : Nat.max init (f x) = init := Nat.max_eq_left hle
        rw [hmax_eq] at h_fold
        rcases ih init m (by simpa [foldlMaxBy] using h_fold) h_lt with ⟨y, hy, hyp, hlen⟩
        exact ⟨y, List.mem_cons_of_mem _ hy, hyp, hlen⟩
      · have h_gt' : init < f x := by omega
        have hmax_eq : Nat.max init (f x) = f x := Nat.max_eq_right (by omega)
        rw [hmax_eq] at h_fold
        by_cases h_m_eq_len : m = f x
        · subst h_m_eq_len; exact ⟨x, by simp, hx, rfl⟩
        · have h_lt' : f x < m := by
            have h_ge : f x ≤ xs.foldl (fun best x => if p x then Nat.max best (f x) else best) (f x) := by
              simpa [foldlMaxBy] using foldlMaxBy_ge xs p f (f x)
            rw [h_fold] at h_ge
            omega
          rcases ih (f x) m (by simpa [foldlMaxBy] using h_fold) h_lt' with ⟨y, hy, hyp, hlen⟩
          exact ⟨y, List.mem_cons_of_mem _ hy, hyp, hlen⟩
    · simp [hx] at h_fold
      rcases ih init m (by simpa [foldlMaxBy] using h_fold) h_lt with ⟨y, hy, hyp, hlen⟩
      exact ⟨y, List.mem_cons_of_mem _ hy, hyp, hlen⟩

/-- `maxMeasureWhere` is `foldlMaxBy` with `init = 0`. -/
def maxMeasureWhere {β : Type} (cands : List β) (len : β → Nat) (p : β → Bool) : Nat :=
  foldlMaxBy cands p len 0

end List

namespace List


/-! ### `foldl` with `Nat.maxBelow` — find maximal element ≤ bound in a list -/

/-- Folding `Nat.maxBelow bound` over `sums` starting from `a` (where `a ≤ bound`)
yields a result ≤ `bound`. -/
lemma foldl_maxBelow_le_bound (bound : Nat) (sums : List Nat) (a : Nat) (ha : a ≤ bound) :
    List.foldl (Nat.maxBelow bound) a sums ≤ bound := by
  induction' sums with x xs ih generalizing a
  · exact ha
  · rw [List.foldl_cons]; apply ih; exact Nat.maxBelow_le_bound bound a x ha

/-- The initial accumulator is ≤ the result of folding `Nat.maxBelow bound`. -/
lemma foldl_maxBelow_ge_acc (bound : Nat) (sums : List Nat) (a : Nat) :
    a ≤ List.foldl (Nat.maxBelow bound) a sums := by
  induction' sums with x xs ih generalizing a
  · exact le_rfl
  · rw [List.foldl_cons]
    have h1 : a ≤ Nat.maxBelow bound a x := Nat.maxBelow_ge_acc bound a x
    have h2 : Nat.maxBelow bound a x ≤ List.foldl (Nat.maxBelow bound) (Nat.maxBelow bound a x) xs :=
      ih (Nat.maxBelow bound a x)
    exact le_trans h1 h2

/-- Any element `s'` in `sums` that is ≤ `bound` is ≤ the foldl result. -/
lemma foldl_maxBelow_ge_s (bound : Nat) (sums : List Nat) (a s' : Nat)
    (hs' : s' ∈ sums) (hsle : s' ≤ bound) :
    s' ≤ List.foldl (Nat.maxBelow bound) a sums := by
  induction' sums with x xs ih generalizing a s'
  · simp at hs'
  · rw [List.foldl_cons]
    cases hs' with
    | head _ =>
      have hx : x ≤ Nat.maxBelow bound a x := Nat.maxBelow_ge_s bound x a hsle
      have hf : Nat.maxBelow bound a x ≤
          List.foldl (Nat.maxBelow bound) (Nat.maxBelow bound a x) xs :=
        foldl_maxBelow_ge_acc bound xs (Nat.maxBelow bound a x)
      exact le_trans hx hf
    | tail _ h => exact ih (Nat.maxBelow bound a x) s' h hsle

/-- The result of `foldl (Nat.maxBelow bound) a sums` is either `a` or some element of `sums`. -/
lemma foldl_maxBelow_result_eq_or_in (bound : Nat) (sums : List Nat) (a : Nat) :
    (List.foldl (Nat.maxBelow bound) a sums = a) ∨
    (List.foldl (Nat.maxBelow bound) a sums ∈ sums) := by
  induction' sums with x xs ih generalizing a
  · left; rfl
  · rw [List.foldl_cons]
    have hfx : Nat.maxBelow bound a x = a ∨ Nat.maxBelow bound a x = x :=
      Nat.maxBelow_eq_or bound a x
    rcases hfx with (hfx | hfx)
    · rw [hfx]; rcases ih a with (h | h)
      · left; exact h
      · right; exact List.mem_cons_of_mem x h
    · rw [hfx]; rcases ih x with (h | h)
      · right; rw [h]; exact List.mem_cons_self x xs
      · right; exact List.mem_cons_of_mem x h

/-! ### `foldl` with `max` — generic `max` on any `LinearOrder` -/

/-- `max a b` is either `a` or `b`. -/
lemma max_eq_or {α : Type} [LinearOrder α] {a b : α} : max a b = a ∨ max a b = b := by
  by_cases h : a ≤ b
  · right; exact max_eq_right h
  · left
    have hlt : b < a := lt_of_not_ge h
    exact max_eq_left (le_of_lt hlt)

/-- `min a b` is either `a` or `b`. Companion to `max_eq_or`. -/
lemma min_eq_or {α : Type} [LinearOrder α] {a b : α} : min a b = a ∨ min a b = b := by
  by_cases h : a ≤ b
  · left; exact min_eq_left h
  · right
    have hlt : b ≤ a := le_of_not_ge h
    exact min_eq_right hlt

/-- The initial accumulator is ≤ the result of folding `max`. -/
lemma foldl_max_ge_init {α : Type} [LinearOrder α] (init : α) (xs : List α) :
    init ≤ List.foldl max init xs := by
  induction xs generalizing init with
  | nil => exact le_refl init
  | cons y ys ih =>
    rw [List.foldl_cons]
    have h1 : init ≤ max init y := le_max_left _ _
    have h2 : max init y ≤ List.foldl max (max init y) ys := ih (max init y)
    exact le_trans h1 h2

/-- `foldl max` is monotone in the initial value: if `a ≤ b`, then
`l.foldl max a ≤ l.foldl max b`. -/
lemma foldl_max_mono {α : Type} [LinearOrder α] {a b : α} (h : a ≤ b) (l : List α) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact h
  | cons y ys ih =>
    rw [List.foldl_cons]
    exact ih (max_le_max h (le_refl y))

/-- Any element in the list is ≤ the result of folding `max`. -/
lemma foldl_max_ge_all {α : Type} [LinearOrder α] (init : α) (xs : List α) (x : α) (hx : x ∈ xs) :
    x ≤ List.foldl max init xs := by
  revert init
  induction hx with
  | head ys =>
    intro init
    rw [List.foldl_cons]
    exact le_trans (le_max_right _ _) (foldl_max_ge_init (max init x) ys)
  | tail y hmem ih =>
    intro init
    rw [List.foldl_cons]
    exact ih (max init y)

/-- `maxBy f init l` folds `max` over `l` after applying `f` to each element:
    `maxBy f init l = l.foldl (fun acc x => max acc (f x)) init`.

    This is a convenience abbreviation for the common pattern of taking the maximum
    of a mapped list with a starting accumulator. -/
def maxBy {α : Type _} (f : α → Nat) (init : Nat) (l : List α) : Nat :=
  List.foldl (fun acc x => max acc (f x)) init l

/-- Folding `(fun acc x => max acc (f x))` starting from `a` yields a result ≥ `a`.
Generalizes `foldl_max_ge_init` (which corresponds to `f = id`). -/
lemma foldl_max_comp_ge_init {α β : Type} [LinearOrder α] (f : β → α) (l : List β) (a : α) :
    a ≤ l.foldl (fun acc x => max acc (f x)) a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    have hax : a ≤ max a (f x) := le_max_left a (f x)
    have hmax : max a (f x) ≤ xs.foldl (fun acc x => max acc (f x)) (max a (f x)) :=
      ih (max a (f x))
    exact le_trans hax hmax

/-- If `p ∈ l`, then `f p ≤ l.foldl (fun acc x => max acc (f x)) a`.
Generalizes `foldl_max_ge_all` (which corresponds to `f = id`). -/
lemma foldl_max_comp_ge_of_mem {α β : Type} [LinearOrder α] (f : β → α) {l : List β} {p : β}
    (h : p ∈ l) (a : α) : f p ≤ l.foldl (fun acc x => max acc (f x)) a := by
  induction l generalizing a with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    rw [List.foldl_cons]
    rw [List.mem_cons] at h
    rcases h with (heq | hxs)
    · rw [heq]
      have hx : f x ≤ max a (f x) := le_max_right a (f x)
      have hfold : max a (f x) ≤ xs.foldl (fun acc x => max acc (f x)) (max a (f x)) :=
        foldl_max_comp_ge_init f xs (max a (f x))
      exact le_trans hx hfold
    · exact (ih hxs (max a (f x)))

/-- `l.foldl (fun acc x => max acc (f x)) init = (l.map f).foldl max init`.
This is the `max`-specialization of `List.foldl_map`, allowing a fold of `max`
over a projected list to be rewritten as a fold over the mapped list. -/
lemma foldl_max_map_eq {α β : Type} [LinearOrder β] (l : List α) (f : α → β) (init : β) :
    l.foldl (fun acc x => max acc (f x)) init = (l.map f).foldl max init :=
  (List.foldl_map f max l init).symm

/-- The result of `foldl max init xs` is either `init` or some element of `xs`. -/
lemma foldl_max_mem_or_eq {α : Type} [LinearOrder α] (init : α) (xs : List α) :
    List.foldl max init xs = init ∨ List.foldl max init xs ∈ xs := by
  induction xs generalizing init with
  | nil => left; rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases ih (max init y) with (h | h)
    · rw [h]
      rcases max_eq_or (a := init) (b := y) with (hmax | hmax)
      · left; rw [hmax]
      · right; rw [hmax]; exact List.mem_cons_self _ _
    · right; exact List.mem_cons_of_mem _ h

/-- The result of `foldl max` on a list is in `init :: xs` and is at least as large as
every element of `init :: xs`. This combines `foldl_max_mem_or_eq`, `foldl_max_ge_init`,
and `foldl_max_ge_all` into a single convenient statement. -/
lemma foldl_max_mem_and_ge_all {α : Type} [LinearOrder α] (init : α) (xs : List α) :
    xs.foldl max init ∈ init :: xs ∧ ∀ x, x ∈ init :: xs → x ≤ xs.foldl max init := by
  constructor
  · rcases foldl_max_mem_or_eq init xs with (h | h)
    · rw [h]; exact by simp
    · exact List.mem_cons_of_mem _ h
  · intro x hx
    have hx_or : x = init ∨ x ∈ xs := by simpa using hx
    rcases hx_or with (h_eq | hx')
    · rw [h_eq]; exact foldl_max_ge_init init xs
    · exact foldl_max_ge_all init xs x hx'

/-- If `init ≤ b` and every element of `xs` is ≤ `b`, then `xs.foldl max init ≤ b`.
This is the "upper bound" companion to `foldl_max_ge_init` and `foldl_max_ge_all`. -/
lemma foldl_max_le {α : Type} [LinearOrder α] (init : α) (xs : List α) (b : α)
    (h_init : init ≤ b) (h_all : ∀ x ∈ xs, x ≤ b) : xs.foldl max init ≤ b := by
  induction xs generalizing init with
  | nil => exact h_init
  | cons y ys ih =>
    rw [List.foldl_cons]
    have hy : y ≤ b := h_all y (by simp)
    have hmax : max init y ≤ b := max_le h_init hy
    have hys : ∀ x ∈ ys, x ≤ b := fun x hx => h_all x (by simp [hx])
    exact ih (max init y) hmax hys

/-- If every element of `l` is ≤ `init`, then `foldl max init l = init`.
This is the equality version of `foldl_max_le`: when the bound `b` equals `init`
and the condition holds, the fold preserves `init` exactly.
Combines `foldl_max_ge_init` and `foldl_max_le`. -/
lemma foldl_max_eq_init_of_forall_le {α : Type} [LinearOrder α] (l : List α) (init : α)
    (h_all_le : ∀ x ∈ l, x ≤ init) : l.foldl max init = init := by
  apply le_antisymm
  · exact foldl_max_le init l init (le_refl init) h_all_le
  · exact foldl_max_ge_init init l

/-- If `curMax` is in `l`, all elements of `l` are ≤ `curMax`, and `init ≤ curMax`,
then `foldl max init l = curMax`. This is the exact-value counterpart of
`foldl_max_le` and `foldl_max_ge_all`: when `curMax` is the actual maximum of `l`,
the fold yields exactly `curMax`. -/
lemma foldl_max_eq_max_of_mem {α : Type} [LinearOrder α] (l : List α) (init curMax : α)
    (h_mem : curMax ∈ l) (h_all_le : ∀ x ∈ l, x ≤ curMax) (h_init_le : init ≤ curMax) :
    l.foldl max init = curMax := by
  apply le_antisymm
  · exact foldl_max_le init l curMax h_init_le h_all_le
  · exact foldl_max_ge_all init l curMax h_mem

/-- For a non-empty list of `Nat`s, `l.foldl max 0` is an element of `l`.
This is a `Nat`-specific corollary of `foldl_max_mem_or_eq`; it uses that `max 0 x = x`
(so `0` drops out of the fold), meaning the result is the maximum element of the list. -/
lemma foldl_max_mem_of_ne_nil (l : List Nat) (hne : l ≠ []) : l.foldl max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rw [List.foldl_cons, Nat.zero_max]
    by_cases hys : ys = []
    · subst hys; simp
    · have h := foldl_max_mem_or_eq y ys
      rcases h with (h_eq | h_mem)
      · rw [h_eq]; exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ h_mem

/-- `foldl max a xs = max a (foldl max 0 xs)` for any `a`, `xs`.
This distributes the accumulator: starting from `a` is equivalent to taking the max of `a`
and the result starting from `0` (since `0` is the identity for `Nat.max`). -/
lemma foldl_max_eq_max_foldl (xs : List Nat) (a : Nat) :
    xs.foldl max a = max a (xs.foldl max 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp
    rw [ih (max a y), ih y, max_assoc]

/-- For any starting value `a` and list `xs`, `xs.foldl max a = max a (xs.foldl max ⊥)`.
This is the generic `OrderBot` generalization of `foldl_max_eq_max_foldl`, which is
`Nat`-specific (using `0` instead of `⊥`). -/
lemma foldl_max_initial {α : Type} [LinearOrder α] [OrderBot α] (a : α) (xs : List α) :
    xs.foldl max a = max a (xs.foldl max ⊥) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    simp
    have h1 := ih (max a x)
    have h2 := ih x
    rw [h1, h2, max_assoc]

/-- Folding `(fun acc x => max acc (f x))` from `a` is equivalent to taking
`max a` of the fold from `0`. Generalizes `foldl_max_eq_max_foldl` to
arbitrary element types with a `Nat`-valued projection `f`. -/
lemma foldl_max_apply_acc (l : List α) (f : α → Nat) (a : Nat) :
    l.foldl (fun acc x => max acc (f x)) a = max a (l.foldl (fun acc x => max acc (f x)) 0) := by
  induction' l with h t ih generalizing a
  · simp
  · simp only [List.foldl]
    have h0 : max 0 (f h) = f h := by simp
    rw [h0]
    rw [ih (max a (f h)), ih (f h)]
    omega

/-- If `0 < a`, then `0 < l.foldl max a` for any list `l`.
This is because `max a x ≥ a > 0` at each step, so the accumulator never drops to zero. -/
lemma foldl_max_pos_of_pos {a : Nat} (ha : 0 < a) (l : List Nat) : 0 < l.foldl max a := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      rw [List.foldl]
      have ha' : 0 < max a x := Nat.lt_of_lt_of_le ha (Nat.le_max_left a x)
      exact ih ha'

/-- If `l` is nonempty and all its elements are positive, then `0 < l.foldl max 0`. -/
lemma foldl_max_pos_of_nonempty (l : List Nat) (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) :
    0 < l.foldl max 0 := by
  rcases l with (rfl | ⟨x, xs⟩)
  · exact absurd rfl hne
  · have hxpos : 0 < x := hpos x (by simp)
    have : (x :: xs).foldl max 0 = xs.foldl max x := by
      simp [List.foldl, Nat.max_eq_right (Nat.zero_le x)]
    rw [this]
    exact foldl_max_pos_of_pos hxpos xs


end List

namespace List

/-! ### Bounded list -/

/-- `boundedList lo hi l` asserts that every element `x` in `l` satisfies `lo ≤ x ∧ x ≤ hi`. -/
def boundedList {α : Type} [LE α] (lo hi : α) (l : List α) : Prop :=
  ∀ x, x ∈ l → (lo ≤ x ∧ x ≤ hi)

end List


namespace List

/-! ### `maximum_of_length_pos` and `minimum_of_length_pos` characterization -/

/-- If `a` is a member of a nonempty list `l` and `x ≤ a` for all `x ∈ l`, then
    `a` equals `l.maximum_of_length_pos`. This complements `le_maximum_of_length_pos_of_mem`
    (from mathlib) with the reverse direction: the only element that's both a member and
    an upper bound for all elements is exactly the maximum. -/
lemma maximum_of_length_pos_eq_of_mem_and_le {l : List α} [LinearOrder α]
    {hpos : 0 < l.length} {a : α} (hmem : a ∈ l) (hle : ∀ x, x ∈ l → x ≤ a) :
    l.maximum_of_length_pos hpos = a := by
  have hmax_withBot : l.maximum = (a : WithBot α) :=
    (List.maximum_eq_coe_iff.mpr ⟨hmem, hle⟩)
  have hcoe_maxpos : (l.maximum_of_length_pos hpos : WithBot α) = l.maximum :=
    List.coe_maximum_of_length_pos hpos
  have h_eq_coe : (l.maximum_of_length_pos hpos : WithBot α) = (a : WithBot α) := by
    rw [hcoe_maxpos, hmax_withBot]
  exact WithBot.coe_inj.mp h_eq_coe

/-- If `a` is a member of a nonempty list `l` and `a ≤ x` for all `x ∈ l`, then
    `a` equals `l.minimum_of_length_pos`. This complements `minimum_of_length_pos_le_of_mem`
    (from mathlib) with the reverse direction: the only element that's both a member and
    a lower bound for all elements is exactly the minimum. -/
lemma minimum_of_length_pos_eq_of_mem_and_le {l : List α} [LinearOrder α]
    {hpos : 0 < l.length} {a : α} (hmem : a ∈ l) (hle : ∀ x, x ∈ l → a ≤ x) :
    l.minimum_of_length_pos hpos = a := by
  have hmin_withTop : l.minimum = (a : WithTop α) :=
    (List.minimum_eq_coe_iff.mpr ⟨hmem, hle⟩)
  have hcoe_minpos : (l.minimum_of_length_pos hpos : WithTop α) = l.minimum :=
    List.coe_minimum_of_length_pos hpos
  have h_eq_coe : (l.minimum_of_length_pos hpos : WithTop α) = (a : WithTop α) := by
    rw [hcoe_minpos, hmin_withTop]
  exact WithTop.coe_inj.mp h_eq_coe

end List

namespace List

/-! ### Minimum of a `List Nat` via `foldr` -/

/-- Compute the minimum of a `List Nat` using `foldr Nat.min`.
Returns `0` for the empty list. -/
def minNat : List Nat → Nat
  | [] => 0
  | h :: t => List.foldr Nat.min h t


lemma minNat_nil : minNat [] = 0 := rfl


lemma minNat_cons (y : Nat) (ys : List Nat) : minNat (y :: ys) = List.foldr Nat.min y ys := rfl


lemma minNat_singleton (x : Nat) : minNat [x] = x := by
  simp [minNat]

/-- If `x ∈ xs`, then `minNat xs ≤ x`. -/
theorem minNat_le_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) : minNat xs ≤ x := by
  have aux (l : List Nat) (a : Nat) :
      l.foldr Nat.min a ≤ a ∧ ∀ x ∈ l, l.foldr Nat.min a ≤ x := by
    induction l with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldr_cons]
      refine ⟨(min_le_right _ _).trans ih.1, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih.2 z hz)
  cases xs with
  | nil => simp at h
  | cons a xs =>
    rcases List.mem_cons.mp h with rfl | h
    · exact (aux xs x).1
    · exact (aux xs a).2 x h

/-! ### Maximum of a `List Nat` via `foldr` -/

/-- Compute the maximum of a `List Nat` using `foldr Nat.max`.
Returns `0` for the empty list. -/
def maxNat : List Nat → Nat
  | [] => 0
  | h :: t => List.foldr Nat.max h t


lemma maxNat_nil : maxNat [] = 0 := rfl


lemma maxNat_cons (y : Nat) (ys : List Nat) : maxNat (y :: ys) = List.foldr Nat.max y ys := rfl


lemma maxNat_singleton (x : Nat) : maxNat [x] = x := by
  simp [maxNat]

/-! ### Minimum non-zero element -/

/-- `minNonZero xs` returns the minimum non-zero element of `xs`.
If all elements are zero (or `xs` is empty), returns `0`.

Uses `xs.foldl Nat.max 0` (the maximum of the list) as the initial accumulator
to avoid `Nat.min 0 x = 0` making the result always `0`. Non-zero elements then
reduce the accumulator via `Nat.min`. -/
def minNonZero (xs : List Nat) : Nat :=
  xs.foldl (fun acc f => if f = 0 then acc else Nat.min acc f) (xs.foldl max 0)

/-! ### Maximum element strictly below a bound -/

/-- Maximum element of `ns` that is strictly smaller than `bound`,
or `0` if no such element exists (or the list is empty).

Example: `maxLt [1, 3, 5, 7] 6 = 5`, `maxLt [1, 3, 5, 7] 1 = 0`. -/
def maxLt (ns : List Nat) (bound : Nat) : Nat :=
  ns.foldl (fun acc x => if x < bound ∧ x > acc then x else acc) 0

lemma maxLt_nil (bound : Nat) : maxLt ([] : List Nat) bound = 0 := rfl

/-! ### Minimum / Maximum with default -/

/-- Return the minimum element of `xs`, or `default` if `xs` is empty. -/
def minWithDefault {α : Type} [LinearOrder α] (default : α) : List α → α
  | [] => default
  | x :: xs => xs.foldl min x

/-- Return the maximum element of `xs`, or `default` if `xs` is empty. -/
def maxWithDefault {α : Type} [LinearOrder α] (default : α) : List α → α
  | [] => default
  | x :: xs => xs.foldl max x

/-- Every element of `l` is ≤ `maxWithDefault default l`. -/
lemma maxWithDefault_ge_of_mem {α : Type} [LinearOrder α] (default : α) {l : List α} {x : α}
    (hx : x ∈ l) : x ≤ maxWithDefault default l := by
  cases l with
  | nil => simp at hx
  | cons a xs => exact (foldl_max_mem_and_ge_all a xs).2 x hx

/-- For a nonempty list, `maxWithDefault default l` is an element of `l`. -/
lemma maxWithDefault_mem {α : Type} [LinearOrder α] (default : α) {l : List α} (hne : l ≠ []) :
    maxWithDefault default l ∈ l := by
  cases l with
  | nil => contradiction
  | cons a xs => exact (foldl_max_mem_and_ge_all a xs).1

/-! ### `maxBot` — maximum with `OrderBot` as default -/

/-- Maximum element of a list, using `⊥` (from `OrderBot`) as the default for empty lists.
Uses structural recursion for convenient induction proofs.
Compare with `maxWithDefault` which takes an explicit default value. -/
def maxBot {α : Type u} [LinearOrder α] [OrderBot α] : List α → α
  | [] => ⊥
  | [x] => x
  | x :: xs => max x (maxBot xs)


lemma maxBot_nil {α : Type u} [LinearOrder α] [OrderBot α] : maxBot ([] : List α) = (⊥ : α) := rfl

lemma maxBot_singleton {α : Type u} [LinearOrder α] [OrderBot α] (x : α) : maxBot [x] = x := rfl

lemma maxBot_cons {α : Type u} [LinearOrder α] [OrderBot α] (x : α) (xs : List α) : maxBot (x :: xs) = max x (maxBot xs) := by
  cases xs with
  | nil => simp [maxBot]
  | cons y ys => rfl

/-- Every element of `l` is ≤ `maxBot l`. -/
lemma le_maxBot_of_mem {α : Type u} [LinearOrder α] [OrderBot α] (l : List α) (c : α) (hc : c ∈ l) : c ≤ maxBot l := by
  induction l with
  | nil => simp at hc
  | cons h t ih =>
    simp at hc
    rcases hc with (rfl | hc')
    · cases t with
      | nil => simp [maxBot]
      | cons h2 t2 => simp [maxBot]
    · have h_le := ih hc'
      cases t with
      | nil => exfalso; exact by simpa using hc'
      | cons h2 t2 =>
        unfold maxBot
        exact le_trans h_le (le_max_right _ _)

/-- If `maxBot l < y`, then every element of `l` is `< y`. -/
lemma lt_of_maxBot_lt {α : Type u} [LinearOrder α] [OrderBot α] (l : List α) (y : α) (hy : maxBot l < y) (c : α) (hc : c ∈ l) : c < y := by
  have hc_le : c ≤ maxBot l := le_maxBot_of_mem l c hc
  exact lt_of_le_of_lt hc_le hy

/-- Relates `List.foldl max a l` to `max a (maxBot l)`.
This is the fundamental identity connecting `foldl max` with the `maxBot` def. -/
theorem foldl_max_eq_max_maxBot {α : Type u} [LinearOrder α] [OrderBot α] (a : α) (l : List α) :
    List.foldl max a l = max a (maxBot l) := by
  induction l generalizing a with
  | nil => simp [maxBot]
  | cons x xs ih =>
    simp [List.foldl_cons, maxBot_cons x xs, ih (max a x), ih x, max_assoc]

/-- If every element of `xs` is ≤ `k`, then `maxBot xs ≤ k`. -/
theorem maxBot_le_of_forall_le {α : Type u} [LinearOrder α] [OrderBot α] (xs : List α) (k : α)
    (h : ∀ x ∈ xs, x ≤ k) : maxBot xs ≤ k := by
  induction' xs with y ys ih
  · simp [maxBot]
  · rw [maxBot_cons]
    have hy : y ≤ k := h y (by simp)
    have hys : maxBot ys ≤ k := ih (fun x hx => h x (by simp [hx]))
    exact max_le hy hys

/-- `maxBot xs = x` iff `x ∈ xs` and every element of `xs` is ≤ `x`. -/
theorem maxBot_eq_of_forall_le {α : Type u} [LinearOrder α] [OrderBot α] (xs : List α) (x : α)
    (hmem : x ∈ xs) (hle : ∀ y ∈ xs, y ≤ x) : maxBot xs = x :=
  le_antisymm (maxBot_le_of_forall_le xs x hle) (le_maxBot_of_mem xs x hmem)

/-- `maxBot l ≤ k` iff every element of `l` is ≤ `k`. -/
theorem maxBot_le_iff {α : Type u} [LinearOrder α] [OrderBot α] (l : List α) (k : α) :
    maxBot l ≤ k ↔ ∀ x ∈ l, x ≤ k := by
  constructor
  · intro h x hx
    exact le_trans (le_maxBot_of_mem l x hx) h
  · exact maxBot_le_of_forall_le l k

/-- For a nonempty list, `maxBot l` is an element of `l`. -/
theorem maxBot_mem_of_nonempty {α : Type u} [LinearOrder α] [OrderBot α] (l : List α) (hne : l ≠ []) :
    maxBot l ∈ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rw [maxBot_cons]
    by_cases hle : maxBot xs ≤ x
    · rw [max_eq_left hle]
      simp
    · have hlt : x < maxBot xs := lt_of_not_ge hle
      rw [max_eq_right (le_of_lt hlt)]
      by_cases hxs : xs = []
      · rw [hxs] at hlt
        have : maxBot [] = (⊥ : α) := rfl
        rw [this] at hlt
        have hbot : (⊥ : α) ≤ x := bot_le
        exact absurd (lt_of_le_of_lt hbot hlt) (lt_irrefl _)
      · exact List.mem_cons_of_mem _ (ih hxs)

/-! ### `maxByChoice` — generic maximum by choice function -/

/-- Recursively find the maximal element of a list according to a binary
choice function `better`. Returns `default` for the empty list.

`better a b` should intuitively return the "better" (larger, or more desirable)
of `a` and `b`. This is more general than `maxWithDefault`, which requires
a `LinearOrder` — `maxByChoice` allows any custom binary choice operation
on any `Inhabited` type.

For example, to find the longest string in a list (breaking ties lexicographically):
`maxByChoice (λ a b => if a.length > b.length then a else if b.length > a.length then b else if a < b then b else a)`. -/
def maxByChoice [Inhabited α] (better : α → α → α) (cs : List α) : α :=
  match cs with
  | [] => default
  | [c] => c
  | c :: cs' => better c (maxByChoice better cs')
termination_by cs.length

/-- Under suitable assumptions on `better` and a transitive, reflexive relation `R`,
every element `w` of a non-empty list `cs` satisfies `R w (maxByChoice better cs)`.
This characterizes how `maxByChoice` relates to the original elements.

The assumptions capture that `better a b` is at least as good as both `a` and `b`
under the preorder `R`, and `R` is reflexive and transitive. -/
lemma maxByChoice_spec [Inhabited α] (better : α → α → α) (R : α → α → Prop)
    (h_refl : ∀ a, R a a)
    (h_trans : ∀ a b c, R a b → R b c → R a c)
    (h_left : ∀ a b, R a (better a b))
    (h_right : ∀ a b, R b (better a b))
    (cs : List α) (hne : cs ≠ []) (w : α) (hw : w ∈ cs) :
    R w (maxByChoice better cs) := by
  revert w hw
  induction' cs with c cs ih
  · intro w hw; exact (hne rfl).elim
  · intro w hw
    simp at hw
    rcases hw with (rfl | hw')
    · by_cases hcs_empty : cs = []
      · rw [hcs_empty]; simp [maxByChoice]; exact h_refl w
      · have hm : maxByChoice better (w :: cs) = better w (maxByChoice better cs) := by
          simp [maxByChoice, hcs_empty]
        rw [hm]
        exact h_left w (maxByChoice better cs)
    · by_cases hcs_empty : cs = []
      · rw [hcs_empty] at hw'; simp at hw'
      · have hm : maxByChoice better (c :: cs) = better c (maxByChoice better cs) := by
          simp [maxByChoice, hcs_empty]
        rw [hm]
        have ih_spec := ih hcs_empty w hw'
        have bc_spec := h_right c (maxByChoice better cs)
        exact h_trans w (maxByChoice better cs) (better c (maxByChoice better cs)) ih_spec bc_spec

/-! ### `min?` on nonempty lists -/

/-- If a list is nonempty, its minimum is not `none`.
For the converse (and the iff version), see `List.min?_eq_none_iff` in mathlib. -/
lemma min?_ne_none {α : Type} [LinearOrder α] {l : List α} (h : l ≠ []) : l.min? ≠ none := by
  simpa [List.min?_eq_none_iff] using h

/-- If `xs.min? = some m` for a list with a `LinearOrder`, then `m` is a member of `xs`
and `m` is less than or equal to every element of `xs`.
This is the forward direction of `List.min?_eq_some_iff`. -/
lemma min?_mem_and_le {α : Type} [LinearOrder α] {xs : List α} {m : α} (h : xs.min? = some m) :
    m ∈ xs ∧ ∀ x ∈ xs, m ≤ x := by
  have h_min_eq_or : ∀ (a b : α), min a b = a ∨ min a b = b := by
    intro a b
    rcases le_total a b with (hle | hle)
    · left; exact min_eq_left hle
    · right; exact min_eq_right hle
  have h_le_min_iff : ∀ (a b c : α), a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
    intro a b c
    constructor
    · intro hle; exact ⟨le_trans hle (min_le_left _ _), le_trans hle (min_le_right _ _)⟩
    · intro ⟨h₁, h₂⟩; exact le_min h₁ h₂
  letI : Std.Antisymm (fun (x1 x2 : α) => x1 ≤ x2) :=
    { antisymm := λ _ _ h₁ h₂ => le_antisymm h₁ h₂ }
  have h_iff := List.min?_eq_some_iff (xs := xs) (a := m)
    (le_refl := fun a : α => le_refl a)
    (min_eq_or := h_min_eq_or)
    (le_min_iff := h_le_min_iff)
  exact h_iff.mp h

/-- If `min?` is not `none`, then `min? = some (min?.getD d)` for any default `d`. -/
lemma min?_getD_eq_of_ne_none {α : Type} [Min α] (l : List α) (d : α) (hne : l.min? ≠ none) :
    l.min? = some (l.min?.getD d) := by
  rcases Option.ne_none_iff_exists'.mp hne with ⟨m, hm⟩
  rw [hm, Option.getD_some]

/-- If a list is nonempty, its maximum is not `none`.
For the converse (and the iff version), see `List.max?_eq_none_iff` in mathlib. -/
lemma max?_ne_none {α : Type} [LinearOrder α] {l : List α} (h : l ≠ []) : l.max? ≠ none := by
  simpa [List.max?_eq_none_iff] using h

/-- If a non-empty list has a maximum, it exists as a plain value (not `⊥`).
The maximum is a member of the list. -/
lemma exists_maximum_of_ne_nil {α : Type} [LinearOrder α] {l : List α} (h : l ≠ []) :
    ∃ x : α, l.maximum = (x : WithBot α) ∧ x ∈ l := by
  have hmax_ne_bot : l.maximum ≠ ⊥ := by
    intro hmax
    apply h
    exact (List.maximum_eq_bot.mp hmax)
  rcases (WithBot.ne_bot_iff_exists.mp hmax_ne_bot) with ⟨x, hx⟩
  refine ⟨x, hx.symm, List.maximum_mem hx.symm⟩

/-- If `l.maximum ≠ ⊥`, then `(l.maximum).unbot h` is a member of `l` and an upper bound
for all elements of `l`. This lemma bridges `List.maximum` (which returns `WithBot α`)
with the membership and upper-bound properties, using `unbot` to extract the value.
Works for any `LinearOrder α`. -/
lemma maximum_unbot_mem_and_le {α : Type} [LinearOrder α] {l : List α} (h_max_bot : l.maximum ≠ ⊥) :
    (l.maximum).unbot h_max_bot ∈ l ∧ ∀ s ∈ l, s ≤ (l.maximum).unbot h_max_bot := by
  let m := (l.maximum).unbot h_max_bot
  have hm_eq : l.maximum = (m : WithBot α) :=
    (WithBot.coe_unbot (l.maximum) h_max_bot).symm
  exact ((List.maximum_eq_coe_iff (l := l) (m := m)).mp hm_eq)

/-- If `l.maximum ≠ ⊥`, then `(l.maximum).unbot h` is a member of `l`.
This is the left conjunct of `maximum_unbot_mem_and_le`. -/
lemma maximum_unbot_mem {α : Type} [LinearOrder α] {l : List α} (h_max_bot : l.maximum ≠ ⊥) :
    (l.maximum).unbot h_max_bot ∈ l :=
  (maximum_unbot_mem_and_le h_max_bot).left

/-- If `l.maximum ≠ ⊥`, then `(l.maximum).unbot h` is an upper bound for all elements of `l`.
This is the right conjunct of `maximum_unbot_mem_and_le`. -/
lemma maximum_unbot_le {α : Type} [LinearOrder α] {l : List α} (h_max_bot : l.maximum ≠ ⊥)
    (x : α) (hx : x ∈ l) : x ≤ (l.maximum).unbot h_max_bot :=
  (maximum_unbot_mem_and_le h_max_bot).right x hx

end List


namespace List

/-! ### Maximum over filtered/mapped lists -/

/-- For any `a` in `xs.filter p`, `f a` is bounded by the `foldl max 0` of
`((xs.filter p).map f)`. This is a convenience combination of `foldl_max_ge_all`
with `List.mem_map` and `List.mem_filter`. -/
lemma foldl_max_ge_of_filter {α : Type u} {xs : List α} {p : α → Bool} (f : α → Nat) :
    ∀ a, a ∈ xs.filter p → f a ≤ ((xs.filter p).map f).foldl max 0 := by
  intro a ha
  have hm : f a ∈ ((xs.filter p).map f) := List.mem_map.mpr ⟨a, ha, rfl⟩
  exact foldl_max_ge_all 0 ((xs.filter p).map f) (f a) hm

/-! ### `max?` on `LinearOrder` -/

/-- `List.max? = some a` iff `a` is in the list and every element of the list is ≤ `a`.
Works for any `LinearOrder α`. This provides the required typeclass arguments
(`Std.Antisymm`, `max_eq_or`, `max_le_iff`) to `List.max?_eq_some_iff` from mathlib. -/
lemma max?_eq_some_iff_linearOrder {α : Type} [LinearOrder α] (xs : List α) (a : α) :
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  have h_anti : Std.Antisymm (fun (x y : α) => x ≤ y) :=
    ⟨fun x y h1 h2 => le_antisymm h1 h2⟩
  have h_max_eq_or : ∀ (a b : α), a ⊔ b = a ∨ a ⊔ b = b := by
    intro a b
    by_cases h : a ≤ b
    · right; exact sup_eq_right.mpr h
    · left; have h' : b ≤ a := (lt_of_not_ge h).le; exact sup_eq_left.mpr h'
  have h_max_le_iff : ∀ (a b c : α), b ⊔ c ≤ a ↔ b ≤ a ∧ c ≤ a := by
    intro a b c; simp
  rw [List.max?_eq_some_iff (anti := h_anti) (le_refl := fun a => le_refl a)
    (max_eq_or := h_max_eq_or) (max_le_iff := h_max_le_iff)]

/-- If `l.max? = some a`, then `a ∈ l`. This is the forward direction of
`max?_eq_some_iff_linearOrder` isolated as a standalone lemma for convenience.
(Note: `List.max?_mem` in Std requires `max_eq_or` as an explicit argument;
this version uses `LinearOrder` instead for ergonomic use.) -/
lemma max?_mem_linearOrder {α : Type} [LinearOrder α] {l : List α} {a : α} (h : l.max? = some a) : a ∈ l :=
  ((max?_eq_some_iff_linearOrder l a).mp h).left

/-- If `l.max? = some a`, then every element of `l` is ≤ `a`. This is the forward direction of
`max?_eq_some_iff_linearOrder` isolated as a standalone lemma for convenience. -/
lemma max?_le_all {α : Type} [LinearOrder α] {l : List α} {a : α} (h : l.max? = some a) : ∀ b ∈ l, b ≤ a :=
  ((max?_eq_some_iff_linearOrder l a).mp h).right

/-- For any nonempty list, `l.max?.getD d` returns a maximum element of `l`:
    it belongs to `l` and every element of `l` is ≤ it.
    The default `d` is only used when the list is empty (ruled out by `hne`). -/
lemma max?_getD_spec {α : Type} [LinearOrder α] (l : List α) (d : α) (hne : l ≠ []) :
    (l.max?.getD d) ∈ l ∧ (∀ x, x ∈ l → x ≤ l.max?.getD d) := by
  let r := l.max?.getD d
  match hmax : l.max? with
  | none =>
    have hempty : l = [] := List.max?_eq_none_iff.mp hmax
    exact (hne hempty).elim
  | some m =>
    have h_eq : r = m := by simp [r, hmax]
    have hmem : m ∈ l := max?_mem_linearOrder hmax
    have hle : ∀ x, x ∈ l → x ≤ m := max?_le_all hmax
    subst h_eq
    exact ⟨hmem, hle⟩

/-- `l.foldl max 0` equals `(l.max?).getD 0` for `List Nat`.
This bridges the `foldl max` idiom (common in iterative code) with the `Option`-based `max?` API.
The proof is a special case of `List.foldl_max` with `Nat.zero_max`. -/
lemma foldl_max_zero_eq_getD_max? {l : List Nat} :
    l.foldl max 0 = Option.getD (l.max?) 0 := by
  have h := List.foldl_max (α := Nat) (l := l) (a := 0)
  rw [Nat.zero_max] at h
  exact h

/-! ### `max?` specialized to `Nat` -/

/-- `List.max?_eq_some_iff_linearOrder` specialized to `Nat`.
This gives a convenient characterization: `l.max? = some a` iff `a` is in `l` and every
element of `l` is ≤ `a`. -/
lemma max?_eq_some_iff_nat (l : List Nat) (a : Nat) : l.max? = some a ↔ a ∈ l ∧ ∀ b ∈ l, b ≤ a :=
  max?_eq_some_iff_linearOrder l a

/-- When `(xs.map f).max? = some m`, there exists an element achieving `m`
and every element `x` satisfies `f x ≤ m`. This bridges `max?` on a mapped list
back to membership in the original list, specialized to `Nat`-valued `f`. -/
lemma max?_eq_some_of_map_nat {α : Type} (xs : List α) (f : α → Nat) (m : Nat)
    (h : (xs.map f).max? = some m) : (∃ x ∈ xs, f x = m) ∧ (∀ x ∈ xs, f x ≤ m) := by
  have hmax_iff := (max?_eq_some_iff_nat (xs.map f) m).mp h
  rcases hmax_iff with ⟨hmem, hle⟩
  rcases List.mem_map.mp hmem with ⟨x, hx, hfx⟩
  exact ⟨⟨x, hx, hfx⟩, λ x hx => hle (f x) (List.mem_map_of_mem f hx)⟩

/-! ### `maximum` on mapped lists -/

/-- If `(l.map f).maximum = some m`, then there exists `a ∈ l` such that
`f a = m` and `f b ≤ m` for all `b ∈ l`. This bridges `List.maximum` on a mapped
list back to membership in the original list. -/
lemma exists_of_maximum_map_eq_some {α β : Type _} [LinearOrder β] {l : List α} {f : α → β} {m : β}
    (hmax : (l.map f).maximum = some m) : ∃ a, a ∈ l ∧ f a = m ∧ ∀ b ∈ l, f b ≤ m := by
  have hmem_and_le := (List.maximum_eq_coe_iff (l := l.map f) (m := m)).mp hmax
  rcases hmem_and_le with ⟨hmem, hle⟩
  rcases List.mem_map.mp hmem with ⟨a, ha, ha_eq⟩
  refine ⟨a, ha, ha_eq, ?_⟩
  intro b hb
  have hb_mem : f b ∈ l.map f := List.mem_map.mpr ⟨b, hb, rfl⟩
  exact hle (f b) hb_mem

/-! ### `maxD` — max-with-default for `List Nat` -/

/-- Computable max-with-default for `List Nat`: returns the maximum of `d` and all elements in `xs`.
This is a `Nat`-specific wrapper around `foldl Nat.max`.
See `maxOn` for the version that applies a function and uses `0` as the default. -/
def maxD (xs : List Nat) (d : Nat) : Nat :=
  xs.foldl Nat.max d


lemma maxD_nil (d : Nat) : maxD [] d = d := rfl

lemma maxD_cons (x : Nat) (xs : List Nat) (d : Nat) : maxD (x :: xs) d = maxD xs (max d x) := rfl

/-- The default value `d` is a lower bound of `maxD xs d`. -/
lemma maxD_ge_default (xs : List Nat) (d : Nat) : d ≤ maxD xs d :=
  foldl_max_ge_init d xs

/-- Every element of `xs` is bounded above by `maxD xs d`. -/
lemma maxD_ge_of_mem {xs : List Nat} {x d : Nat} (h : x ∈ xs) : x ≤ maxD xs d :=
  foldl_max_ge_all d xs x h

/-- If `a` and `b` are both in `xs`, then `max a b ≤ maxD xs d`.
This is a convenience lemma combining `maxD_ge_of_mem` for two elements. -/
lemma maxD_max_le_of_mem {xs : List Nat} {a b d : Nat} (ha : a ∈ xs) (hb : b ∈ xs) :
    max a b ≤ maxD xs d :=
  max_le (maxD_ge_of_mem ha) (maxD_ge_of_mem hb)

/-- `maxD xs d ≤ M ↔ d ≤ M ∧ ∀ x ∈ xs, x ≤ M`.
Characterizes when the maximum of `d` and all elements in `xs` is bounded by `M`. -/
lemma maxD_le_iff (xs : List Nat) (d M : Nat) :
    maxD xs d ≤ M ↔ d ≤ M ∧ ∀ x ∈ xs, x ≤ M := by
  constructor
  · intro h
    refine ⟨le_trans (maxD_ge_default xs d) h, fun x hx => le_trans (maxD_ge_of_mem hx) h⟩
  · intro ⟨hd_le, h_all⟩
    induction xs generalizing d with
    | nil => exact hd_le
    | cons x xs ih =>
      rw [maxD_cons]
      have hx_le : x ≤ M := h_all x (by simp)
      have hmax_le : max d x ≤ M := by omega
      have h_all_tail : ∀ y ∈ xs, y ≤ M := fun y hy => h_all y (by simp [hy])
      exact ih (max d x) hmax_le h_all_tail

/-- `maxD (xs ++ ys) d = max (maxD xs d) (maxD ys d)`.
The maximum over a concatenation equals the max of the maximums over each part. -/
lemma maxD_append (xs ys : List Nat) (d : Nat) :
    maxD (xs ++ ys) d = max (maxD xs d) (maxD ys d) := by
  rw [maxD, maxD, maxD, List.foldl_append]
  rw [foldl_max_eq_max_foldl ys (xs.foldl Nat.max d)]
  have h : xs.foldl Nat.max d ≥ d := foldl_max_ge_init d xs
  rw [show ys.foldl Nat.max d = max d (ys.foldl Nat.max 0) from foldl_max_eq_max_foldl ys d]
  rw [← max_assoc, max_eq_left h]

/-! ### `listMax` — maximum element of a `List Nat` -/

/-- Maximum element of a `List Nat`, returning `0` for the empty list.
Equivalent to `maxWithDefault 0`; uses `foldl Nat.max` starting from the first element. -/
def listMax (l : List Nat) : Nat := maxWithDefault 0 l

lemma listMax_nil : listMax [] = 0 := rfl

lemma listMax_cons (x : Nat) (xs : List Nat) : listMax (x :: xs) = xs.foldl Nat.max x := rfl

/-- Alternative form of `listMax_cons` using `max h (listMax t)`. -/
lemma listMax_cons' (h : Nat) (t : List Nat) : listMax (h :: t) = max h (listMax t) := by
  rw [listMax_cons, foldl_max_eq_max_foldl t h]
  congr
  induction t with
  | nil => rfl
  | cons x xs _ =>
    simp [listMax, maxWithDefault, List.foldl, Nat.max_comm]

lemma listMax_singleton (n : Nat) : listMax [n] = n := by
  simp [listMax_cons', listMax_nil]

lemma listMax_append (l₁ l₂ : List Nat) : listMax (l₁ ++ l₂) = max (listMax l₁) (listMax l₂) := by
  induction' l₁ with h t ih
  · simp [listMax_nil]
  · simp [listMax_cons', ih, max_assoc]

/-- `listMax (l.map f)` is equivalent to folding `max` over `f a` for each `a ∈ l`. -/
lemma listMax_map_eq_foldl (l : List α) (f : α → Nat) :
    listMax (l.map f) = l.foldl (fun acc x => max acc (f x)) 0 := by
  induction' l with h t ih
  · rfl
  · simp [List.map_cons, listMax_cons', ih, List.foldl_cons]
    rw [← foldl_max_apply_acc t f (f h)]

/-- Every element of `l` is ≤ `listMax l`. -/
lemma listMax_ge_of_mem {x : Nat} {l : List Nat} (hx : x ∈ l) : x ≤ listMax l := by
  cases l with
  | nil => simp at hx
  | cons head tail =>
    simp [listMax]
    have hx_cases : x = head ∨ x ∈ tail := by simpa using hx
    cases hx_cases with
    | inl h_eq =>
      rw [h_eq]
      exact foldl_max_ge_init head tail
    | inr h_mem =>
      exact foldl_max_ge_all head tail x h_mem

/-- If every element of `l` is ≤ `b`, then `listMax l ≤ b`.
This is the "upper bound" companion to `listMax_ge_of_mem`. -/
lemma listMax_le_of_forall_le {l : List Nat} {b : Nat} (h : ∀ x ∈ l, x ≤ b) : listMax l ≤ b := by
  cases l with
  | nil => simp [listMax, maxWithDefault]
  | cons y ys =>
    rw [listMax_cons]
    have hy : y ≤ b := h y (by simp)
    have hys : ∀ x ∈ ys, x ≤ b := fun x hx => h x (by simp [hx])
    exact foldl_max_le y ys b hy hys

/-- Cons preserves the `listMax` upper bound: if `listMax (x :: xs) < t`, then `listMax xs < t`.
This follows because prepending an element can only increase the maximum. -/
lemma listMax_cons_lt (x : Nat) (xs : List Nat) (t : Nat) (h : listMax (x :: xs) < t) : listMax xs < t := by
  have hle : listMax xs ≤ listMax (x :: xs) :=
    listMax_le_of_forall_le fun y hy => listMax_ge_of_mem (List.mem_cons_of_mem x hy)
  omega

/-- For a nonempty list, `listMax l` is itself an element of `l`. -/
lemma listMax_mem_of_nonempty {l : List Nat} (hne : l ≠ []) : listMax l ∈ l := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    have h := foldl_max_mem_or_eq x xs
    rcases h with (h_eq | h_mem)
    · have : listMax (x :: xs) = x := by
        simp [listMax, maxWithDefault, h_eq]
      rw [this]
      exact List.mem_cons_self _ _
    · have : listMax (x :: xs) = xs.foldl Nat.max x := by
        simp [listMax, maxWithDefault]
      rw [this]
      exact List.mem_cons_of_mem _ h_mem

/-- For any function `f : Nat → Nat`, the value `f j` is at most `listMax (List.map f (List.range n))`
whenever `j < n`. This is a convenient wrapper combining `listMax_ge_of_mem`, `List.mem_map`, and
`List.mem_range`. -/
lemma listMax_map_range_ge (f : Nat → Nat) (n j : Nat) (hj : j < n) :
    f j ≤ listMax (List.map f (List.range n)) := by
  have hmem : f j ∈ List.map f (List.range n) :=
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  exact listMax_ge_of_mem hmem

/-- For any function `f : Nat → Nat` and positive `n`, the maximum of
`List.map f (List.range n)` is achieved at some index `i < n`. -/
lemma listMax_map_range_exists_eq (f : Nat → Nat) (n : Nat) (hn : 1 ≤ n) :
    ∃ i, i < n ∧ f i = listMax (List.map f (List.range n)) := by
  have hrange_nonempty : List.range n ≠ [] := by
    intro h
    rw [List.range_eq_nil] at h
    omega
  have hmap_nonempty : List.map f (List.range n) ≠ [] := by
    intro hmap
    apply hrange_nonempty
    exact (List.map_eq_nil_iff (f := f)).mp hmap
  have hmax_mem : listMax (List.map f (List.range n)) ∈ List.map f (List.range n) :=
    listMax_mem_of_nonempty hmap_nonempty
  rcases List.mem_map.mp hmax_mem with ⟨i, hi_range, hi_eq⟩
  have hi_len : i < n := by
    rw [List.mem_range] at hi_range
    exact hi_range
  exact ⟨i, hi_len, hi_eq⟩

/-- `listMax (l.map f)` is either 0, or there exists an element in `l` whose `f`-value
equals the maximum. Unlike `listMax_mem_of_nonempty`, this handles the empty-list case
gracefully via the disjunction. -/
lemma listMax_map_eq_zero_or_exists_mem {α : Type u} (f : α → Nat) (l : List α) :
    listMax (l.map f) = 0 ∨ ∃ x ∈ l, f x = listMax (l.map f) := by
  by_cases h : l = []
  · subst l; left; rfl
  · right
    exact List.mem_map.mp (listMax_mem_of_nonempty (by simpa using h))

/-! ### Sum properties for `List Nat` -/

/-- Every element of a `List Nat` is ≤ the sum of the list. -/
lemma sum_ge_of_mem {x : Nat} {l : List Nat} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons head tail ih =>
    simp at hx ⊢
    have hx_cases : x = head ∨ x ∈ tail := by simpa using hx
    cases hx_cases with
    | inl h_eq => rw [h_eq]; omega
    | inr h_mem =>
      have h := ih h_mem
      omega

/-- The maximum element of a `List Nat` is ≤ the sum of the list. -/
lemma listMax_le_sum (l : List Nat) : listMax l ≤ l.sum := by
  by_cases hne : l = []
  · subst hne; simp [listMax, maxWithDefault]
  · have hmem : listMax l ∈ l := listMax_mem_of_nonempty hne
    exact sum_ge_of_mem hmem

/-! ### `maxBySum` — element with maximum sum from a list of lists -/

/-- From a list of lists, return the element whose `List.sum` is greatest.
Returns `[]` when the input list is empty.
General over any `α` with `AddCommMonoid` and `LinearOrder`. -/
def maxBySum {α : Type u} [AddCommMonoid α] [LinearOrder α] (l : List (List α)) : List α :=
  match l with
  | [] => []
  | [x] => x
  | x :: y :: ys =>
    if List.sum x ≥ List.sum (maxBySum (y :: ys)) then x else maxBySum (y :: ys)

/-- For a nonempty list of lists, `maxBySum l` is itself an element of `l`. -/
lemma maxBySum_mem {α : Type u} [AddCommMonoid α] [LinearOrder α] (l : List (List α)) (h : l ≠ []) :
    maxBySum l ∈ l := by
  induction l with
  | nil => exact (h rfl).elim
  | cons x xs ih =>
    match xs with
    | [] => simp [maxBySum]
    | y :: ys =>
      by_cases hcmp : List.sum x ≥ List.sum (maxBySum (y :: ys))
      · have heq : maxBySum (x :: y :: ys) = x := by
          simp [maxBySum, hcmp]
        rw [heq]
        simp
      · have heq : maxBySum (x :: y :: ys) = maxBySum (y :: ys) := by
          simp [maxBySum, hcmp]
        rw [heq]
        have hne : y :: ys ≠ [] := by simp
        have hmem := ih hne
        exact List.mem_cons_of_mem x hmem

/-- Among all elements of a list of lists, `maxBySum l` has the maximum sum.
That is, for any `s ∈ l`, `List.sum (maxBySum l) ≥ List.sum s`. -/
lemma maxBySum_ge_all {α : Type u} [AddCommMonoid α] [LinearOrder α]
    (l : List (List α)) (s : List α) (hs : s ∈ l) : List.sum (maxBySum l) ≥ List.sum s := by
  induction l generalizing s with
  | nil => simp at hs
  | cons hd tl ih =>
    simp at hs
    rcases hs with (h_eq | hs)
    · -- h_eq: hd = s
      rw [h_eq]
      match tl with
      | [] => simp [maxBySum]
      | hd2 :: tl2 =>
        by_cases hcmp : List.sum hd ≥ List.sum (maxBySum (hd2 :: tl2))
        · have heq' : maxBySum (hd :: hd2 :: tl2) = hd := by
            simp [maxBySum, hcmp]
          rw [heq']
        · have heq' : maxBySum (hd :: hd2 :: tl2) = maxBySum (hd2 :: tl2) := by
            simp [maxBySum, hcmp]
          rw [heq']
          exact le_of_not_ge hcmp
    · -- hs: s ∈ tl
      match tl with
      | [] => simp at hs
      | hd2 :: tl2 =>
        by_cases hcmp : List.sum hd ≥ List.sum (maxBySum (hd2 :: tl2))
        · have heq' : maxBySum (hd :: hd2 :: tl2) = hd := by
            simp [maxBySum, hcmp]
          rw [heq']
          have hge : List.sum (maxBySum (hd2 :: tl2)) ≥ List.sum s := ih s hs
          exact le_trans hge hcmp
        · have heq' : maxBySum (hd :: hd2 :: tl2) = maxBySum (hd2 :: tl2) := by
            simp [maxBySum, hcmp]
          rw [heq']
          exact ih s hs

/-! ### `foldr` with `max` on `Nat` -/

/-- For a non-empty list of `Nat`s, `l.foldr max 0` is a member of `l` and is an upper bound
for all elements of `l`. This is the `foldr` counterpart of `foldl_max_mem_and_ge_all`
(specialized to `Nat` with `init = 0`). -/
lemma foldr_max_spec_of_ne_nil {l : List Nat} (h : l ≠ []) :
    l.foldr max 0 ∈ l ∧ ∀ a ∈ l, a ≤ l.foldr max 0 := by
  have h_eq : (WithBot.some (l.foldr max 0) : WithBot Nat) = l.maximum := by
    simpa using List.foldr_max_of_ne_nil h
  exact (List.maximum_eq_coe_iff (m := l.foldr max 0)).mp h_eq.symm

/-- For a non-empty list of `Nat`s, `l.foldr max 0` is an element of `l`.
Corollary of `foldr_max_spec_of_ne_nil`. -/
lemma foldr_max_mem_of_ne_nil {l : List Nat} (h : l ≠ []) : l.foldr max 0 ∈ l :=
  (foldr_max_spec_of_ne_nil h).left

/-- For a non-empty list of `Nat`s, every element of `l` is ≤ `l.foldr max 0`.
Corollary of `foldr_max_spec_of_ne_nil`. -/
lemma foldr_max_ge_all_of_ne_nil {l : List Nat} (h : l ≠ []) : ∀ a ∈ l, a ≤ l.foldr max 0 :=
  (foldr_max_spec_of_ne_nil h).right

end List


namespace List

/-! ### `max_mem_cons_of_mem` — max of element and head is in the cons -/

/-- If `r ∈ xs` then `max x r ∈ x :: xs`. -/
lemma max_mem_cons_of_mem {α : Type u} [LinearOrder α] {x r : α} {xs : List α} (hmem : r ∈ xs) : max x r ∈ x :: xs := by
  by_cases h : x ≤ r
  · rw [max_eq_right h]
    exact List.mem_cons_of_mem x hmem
  · have h' : r ≤ x := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left h']
    simp

end List

namespace List

/-! # List minimum and width (range)

This module provides `listMin` (the `Nat`-specialized alias of `minWithDefault 0`),
and `width` (range of a list), along with basic lemmas.
-/

/-- Minimum element of a list of natural numbers; returns `0` for the empty list.
This is the dual of `listMax` and is defined as `minWithDefault 0`. -/
def listMin (l : List Nat) : Nat := minWithDefault 0 l

/-! ### Generic `foldMin` — fold `min` starting from a default

Unlike `minWithDefault` (which uses `default` only for the empty list), `foldMin`
folds `min` starting with `default` as the initial accumulator. This means `default`
participates in the `min` computation even for non-empty lists:
`foldMin default [x] = min default x`.

This is useful when folding a list with a sentinel or upper-bound value. -/

/-- Fold `min` over a list starting from `default` as the initial accumulator.
Returns `default` for the empty list, `min default (min of elements)` for non-empty lists. -/
def foldMin [Min α] (default : α) (l : List α) : α :=
  l.foldl (fun a b => min a b) default


lemma foldMin_nil [Min α] (default : α) : foldMin default [] = default := by
  simp [foldMin]


lemma foldMin_singleton [Min α] (default x : α) : foldMin default [x] = min default x := by
  simp [foldMin]

/-! ### `foldMax` — fold `max` starting from a default

This is the dual of `foldMin`. It folds `max` starting with `default` as the initial
accumulator, so `foldMax default [x] = max default x`. -/

/-- Fold `max` over a list starting from `default` as the initial accumulator.
Returns `default` for the empty list, `max default (max of elements)` for non-empty lists.
This is the dual of `foldMin`. -/
def foldMax [Max α] (default : α) (l : List α) : α :=
  l.foldl (fun a b => max a b) default


lemma foldMax_nil [Max α] (default : α) : foldMax default [] = default := by
  simp [foldMax]


lemma foldMax_singleton [Max α] (default x : α) : foldMax default [x] = max default x := by
  simp [foldMax]

/-- `foldMax` composed with `map` equals a fold with `max` on mapped values.
`foldMax default (xs.map f) = xs.foldl (fun acc x => max acc (f x)) default`.
This is essentially `List.foldl_map` applied to `foldMax`. -/
lemma foldMax_map_eq_foldl {α β : Type u} [Max α] (default : α) (xs : List β) (f : β → α) :
    foldMax default (xs.map f) = xs.foldl (fun acc x => max acc (f x)) default := by
  unfold foldMax
  rw [List.foldl_map]

/-! ### `maxVal` — maximum value of a function over a list -/

/-- Maximum value of `f` applied to elements of `ws`.
Returns `0` for the empty list.
Unlike `foldMax`, the default `0` is only used for the empty list; for a singleton
`[w]`, the result is `f w` (not `max 0 (f w)`). -/
def maxVal (f : α → Nat) (ws : List α) : Nat :=
  match ws with
  | [] => 0
  | [w] => f w
  | w :: ws' => max (f w) (maxVal f ws')


lemma maxVal_nil (f : α → Nat) : maxVal f [] = 0 := rfl


lemma maxVal_singleton (f : α → Nat) (w : α) : maxVal f [w] = f w := rfl

/-- When the list is nonempty, `maxVal f ws` is an upper bound for all `f w`
and is attained by some element. -/
lemma maxVal_spec (f : α → Nat) (ws : List α) (hne : ws ≠ []) :
    (∀ w ∈ ws, f w ≤ maxVal f ws) ∧
    (∃ w ∈ ws, f w = maxVal f ws) := by
  induction' ws with w ws' IH
  · exact (hne rfl).elim
  · cases' ws' with w' ws''
    · simp [maxVal]
    · have h_ih := IH (by simp)
      rcases h_ih with ⟨hle, hex⟩
      rcases hex with ⟨wmax, hwmax_mem, hwmax_eq⟩
      dsimp [maxVal]
      have max_choice := max_choice (f w) (maxVal f (w' :: ws''))
      constructor
      · intro x hx
        have hx_cases := (List.mem_cons (a := x) (b := w) (l := w' :: ws'')).mp hx
        rcases hx_cases with (rfl | hx_in)
        · exact le_max_left _ _
        · have hxle := hle x hx_in
          exact le_trans hxle (le_max_right _ _)
      · rcases max_choice with (h | h)
        · exact ⟨w, by simp, h.symm⟩
        · have heq : f wmax = max (f w) (maxVal f (w' :: ws'')) := by
            calc
              f wmax = maxVal f (w' :: ws'') := hwmax_eq
              _ = max (f w) (maxVal f (w' :: ws'')) := h.symm
          exact ⟨wmax, by simp [hwmax_mem], heq⟩

/-! ### Convenience lemmas for `maxVal` -/

/-- Every element's measure is ≤ `maxVal f ws`. Works for all lists (vacuously true for empty). -/
lemma maxVal_ge (f : α → Nat) (ws : List α) : ∀ w ∈ ws, f w ≤ maxVal f ws := by
  by_cases hne : ws = []
  · subst hne; simp
  · exact (maxVal_spec f ws hne).1

/-- For a nonempty list, there exists an element achieving `maxVal f ws`. -/
lemma maxVal_exists (f : α → Nat) (ws : List α) (hne : ws ≠ []) : ∃ w ∈ ws, f w = maxVal f ws :=
  (maxVal_spec f ws hne).2

/-- Unfolding lemma: `maxVal f (x :: xs) = max (f x) (maxVal f xs)`.
This holds for all `xs`, including the empty case where `maxVal f [] = 0`. -/
lemma maxVal_cons (f : α → Nat) (x : α) (xs : List α) :
    maxVal f (x :: xs) = max (f x) (maxVal f xs) := by
  cases xs with
  | nil => simp [maxVal]
  | cons y ys => simp [maxVal]

/-! ### Additional lemmas about `maxVal` -/

/-- If `maxVal f ws > 0`, then the list is nonempty. -/
lemma ne_nil_of_maxVal_pos (f : α → Nat) (ws : List α) (hpos : maxVal f ws > 0) :
    ws ≠ [] := by
  intro h; subst h; simp [maxVal] at hpos

/-- If the maximum is positive, then it is attained at some element.
This is the `> 0` variant of `maxVal_exists` (which requires `ws ≠ []`). -/
lemma maxVal_pos_exists (f : α → Nat) (ws : List α) (hpos : maxVal f ws > 0) :
    ∃ w ∈ ws, f w = maxVal f ws :=
  maxVal_exists f ws (ne_nil_of_maxVal_pos f ws hpos)

/-- If every element maps to `0`, then `maxVal f ws = 0`. -/
lemma maxVal_eq_zero_of_forall {f : α → Nat} {ws : List α} (h : ∀ w ∈ ws, f w = 0) :
    maxVal f ws = 0 := by
  induction' ws with x xs ih
  · rfl
  · have hx : f x = 0 := h x (by simp)
    have hxs : ∀ w ∈ xs, f w = 0 := fun w hw => h w (by simp [hw])
    rw [maxVal_cons, hx, ih hxs, max_self]

/-- There exists a positive natural number strictly greater than `f x` for all `x ∈ ws`.
For nonempty lists this is `maxVal f ws + 1`; for empty lists any positive number works.
This is useful when a strict upper bound on a finite set of `Nat`-valued measures is needed. -/
lemma exists_nat_gt_maxVal (f : α → Nat) (ws : List α) : ∃ n : Nat, 0 < n ∧ ∀ w ∈ ws, f w < n := by
  refine ⟨maxVal f ws + 1, by omega, λ w hw => ?_⟩
  have hle := maxVal_ge f ws w hw
  omega

/-! ### `max`/`min` bound lemma for `cons`

Given that `m` is an upper bound of `ys` and is attained by some element in `ys`,
`max x m` is an upper bound of `x :: ys` and is also attained. This is the key
inductive step when proving that a recursively computed maximum over a list is
correct. -/

/-- If `m` is an upper bound of `ys` and is attained at some element,
then `max x m` is an upper bound of `x :: ys` and is attained. -/
lemma max_bound_cons {α : Type _} [LinearOrder α] {x m : α} {ys : List α}
    (h_bound : ∀ z ∈ ys, z ≤ m) (h_attain : ∃ z ∈ ys, z = m) :
    (∀ z ∈ x :: ys, z ≤ max x m) ∧ (∃ z ∈ x :: ys, z = max x m) := by
  constructor
  · intro z hz
    rw [List.mem_cons] at hz
    rcases hz with (rfl | hz')
    · exact le_max_left _ _
    · have hz_le_m : z ≤ m := h_bound z hz'
      exact le_trans hz_le_m (le_max_right _ _)
  · by_cases h : m ≤ x
    · have hmax_eq : max x m = x := max_eq_left h
      rw [hmax_eq]
      exact ⟨x, by simp, rfl⟩
    · have hx_le_m : x ≤ m := by
        rcases le_total x m with (hx | hm)
        · exact hx
        · exact absurd hm h
      have hmax_eq : max x m = m := max_eq_right hx_le_m
      rw [hmax_eq]
      rcases h_attain with ⟨z, hz, hz_eq⟩
      exact ⟨z, by simp [hz], hz_eq⟩

/-! ### Basic lemmas -/

/-- `listMin` of the empty list is `0`. -/

lemma listMin_nil : listMin ([] : List Nat) = 0 := rfl

/-- `listMin` of a nonempty list re-expresssed via `foldl Nat.min`. -/
lemma listMin_cons (x : Nat) (xs : List Nat) : listMin (x :: xs) = xs.foldl Nat.min x := rfl

/-! ### Singleton lemmas -/

/-- `listMin` of a singleton list returns that element. -/

lemma listMin_singleton (x : Nat) : listMin [x] = x := by
  simp [listMin, minWithDefault]

/-! ### Membership lemmas for `listMin` -/

/-- If `x` is an element of `l`, then `listMin l ≤ x`.
In other words, `listMin` is a lower bound for all elements of `l`. -/
lemma listMin_le_of_mem {x : ℕ} {l : List ℕ} (h : x ∈ l) : listMin l ≤ x := by
  cases l with
  | nil => simp at h
  | cons a xs =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldMin_le_initial xs x
    · exact foldMin_le_member xs a x h

/-- For any function `f : α → ℕ`, if `x ∈ xs` then `listMin (map f xs) ≤ f x`.
This is a convenient corollary of `listMin_le_of_mem` for mapped lists. -/
lemma listMin_le_of_mem_map {α : Type} (f : α → ℕ) {xs : List α} {x : α} (hx : x ∈ xs) :
    listMin (List.map f xs) ≤ f x := by
  apply listMin_le_of_mem
  exact List.mem_map_of_mem f hx

/-! ### `minWithDefault` lemmas (generic `LinearOrder`)

These are the duals of the `maxWithDefault_ge_of_mem` / `maxWithDefault_mem` lemmas
from `general.List`, providing lower-bound and membership properties for `minWithDefault`. -/

/-- The result of `foldl min x xs` is either `x` or an element of `xs`.
This is the generic `LinearOrder` version of `List.foldl_min_mem` (which is `Nat`-only). -/
lemma foldl_min_eq_or_mem {α : Type} [LinearOrder α] (x : α) (xs : List α) :
    xs.foldl min x = x ∨ xs.foldl min x ∈ xs := by
  induction xs generalizing x with
  | nil => left; rfl
  | cons y ys ih =>
    have h := ih (min x y)
    rcases h with (h_eq | h_mem)
    · by_cases hxy : x ≤ y
      · left
        calc
          (y :: ys).foldl min x = ys.foldl min (min x y) := rfl
          _ = min x y := h_eq
          _ = x := min_eq_left hxy
      · right
        have h_eq' : (y :: ys).foldl min x = y :=
          calc
            (y :: ys).foldl min x = ys.foldl min (min x y) := rfl
            _ = min x y := h_eq
            _ = y := min_eq_right (le_of_not_ge hxy)
        rw [h_eq']
        simp
    · right
      have h_mem' : ys.foldl min (min x y) ∈ (y :: ys) := List.mem_cons_of_mem y h_mem
      simpa [List.foldl] using h_mem'

/-- For a nonempty list, `minWithDefault default l` is an element of `l`.
This is the dual of `maxWithDefault_mem`. -/
lemma minWithDefault_mem {α : Type} [LinearOrder α] (default : α) {l : List α} (hne : l ≠ []) :
    minWithDefault default l ∈ l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    simpa [minWithDefault] using
      (foldl_min_eq_or_mem x xs).elim (fun h => by rw [h]; exact List.mem_cons_self _ _)
        (fun h => List.mem_cons_of_mem _ h)

/-- The result of `foldl max x xs` is either `x` or an element of `xs`.
This is the `max` dual of `foldl_min_eq_or_mem`. -/
lemma foldl_max_eq_or_mem {α : Type} [LinearOrder α] (x : α) (xs : List α) :
    xs.foldl max x = x ∨ xs.foldl max x ∈ xs := by
  induction xs generalizing x with
  | nil => left; rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    have h := ih (max x y)
    rcases h with (h_eq | h_mem)
    · by_cases hxy : x ≤ y
      · right
        have hval : ys.foldl max (max x y) = y := by
          calc
            ys.foldl max (max x y) = max x y := h_eq
            _ = y := max_eq_right hxy
        rw [hval]
        simp
      · left
        calc
          ys.foldl max (max x y) = max x y := h_eq
          _ = x := max_eq_left (le_of_not_ge hxy)
    · right; exact List.mem_cons_of_mem y h_mem

/-- If `x` is an element of `l`, then `minWithDefault default l ≤ x`.
In other words, `minWithDefault` is a lower bound for all elements of `l`.
This is the dual of `maxWithDefault_ge_of_mem`. -/
lemma minWithDefault_le_of_mem {α : Type} [LinearOrder α] (default : α) {l : List α} {x : α}
    (hx : x ∈ l) : minWithDefault default l ≤ x := by
  cases l with
  | nil => simp at hx
  | cons a xs =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact foldMin_le_initial xs x
    · exact foldMin_le_member xs a x hx

/-! ### Width (range of a list) -/

/-- Width (range) of a list: the difference between its maximum and minimum;
    `0` for the empty list. -/
def width (s : List Nat) : Nat :=
  match s with
  | [] => 0
  | _  => listMax s - listMin s

/-- `width` for the empty list is `0`. -/

lemma width_nil : width ([] : List Nat) = 0 := rfl

/-- `width` for a singleton list is `0` (max = min). -/

lemma width_singleton (x : Nat) : width [x] = 0 := by
  unfold width
  simp [listMax, listMin, maxWithDefault, minWithDefault]

/-! ### `listMaxOf` — maximum element satisfying a predicate

`listMaxOf p l` finds the maximum element in `l` that satisfies predicate `p`,
returning `none` if no element satisfies `p`. This generalizes `listMax` (which
works only for `Nat` and considers all elements) to any `LinearOrder` with an
arbitrary decidable predicate.
-/

/-- Finds the maximum element in `l` that satisfies decidable predicate `p`,
    or `none` if no element satisfies `p`. -/
def listMaxOf [LinearOrder α] {p : α → Prop} [DecidablePred p] : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      match listMaxOf (p := p) xs with
      | none => some x
      | some y => some (max x y)
    else
      listMaxOf (p := p) xs

/-- Correctness property for `listMaxOf`:
- If it returns `some m`, then `m ∈ l`, `p m`, and `m` is an upper bound for all `x ∈ l` satisfying `p`.
- If it returns `none`, then no element in `l` satisfies `p`. -/
lemma listMaxOf_prop [LinearOrder α] {p : α → Prop} [DecidablePred p] (l : List α) :
    (∃ m, listMaxOf (p := p) l = some m ∧ m ∈ l ∧ p m ∧ ∀ x ∈ l, p x → x ≤ m) ∨
    (listMaxOf (p := p) l = none ∧ ∀ x ∈ l, ¬ p x) := by
  induction l with
  | nil =>
    right
    simp [listMaxOf]
  | cons x xs ih =>
    by_cases hx : p x
    · rcases ih with (⟨m, hm_eq, hm_mem, hm_p, hm_max⟩ | ⟨hm_none, hm_all⟩)
      · have h_res : listMaxOf (p := p) (x :: xs) = some (max x m) := by
          simp [listMaxOf, hx, hm_eq]
        rw [h_res]
        left
        refine ⟨max x m, rfl, ?_, ?_, ?_⟩
        · rcases le_total x m with (hle | hle)
          · rw [max_eq_right hle]; exact List.mem_cons_of_mem _ hm_mem
          · rw [max_eq_left hle]; exact List.mem_cons_self _ _
        · rcases le_total x m with (hle | hle)
          · rw [max_eq_right hle]; exact hm_p
          · rw [max_eq_left hle]; exact hx
        · intro y hy_mem hy_p
          cases hy_mem with
          | head _ => exact le_max_left _ _
          | tail _ hy_mem' =>
            have hy_le_m : y ≤ m := hm_max y hy_mem' hy_p
            have hm_le_max : m ≤ max x m := le_max_right _ _
            exact le_trans hy_le_m hm_le_max
      · have h_res : listMaxOf (p := p) (x :: xs) = some x := by
          simp [listMaxOf, hx, hm_none]
        rw [h_res]
        left
        refine ⟨x, rfl, List.mem_cons_self _ _, hx, ?_⟩
        intro y hy_mem hy_p
        cases hy_mem with
        | head _ => exact le_refl x
        | tail _ hy_mem' => exfalso; exact hm_all y hy_mem' hy_p
    · rcases ih with (⟨m, hm_eq, hm_mem, hm_p, hm_max⟩ | ⟨hm_none, hm_all⟩)
      · have h_res : listMaxOf (p := p) (x :: xs) = some m := by
          simp [listMaxOf, hx, hm_eq]
        rw [h_res]
        left
        refine ⟨m, rfl, List.mem_cons_of_mem _ hm_mem, hm_p, ?_⟩
        intro y hy_mem hy_p
        cases hy_mem with
        | head _ => exfalso; exact hx hy_p
        | tail _ hy_mem' => exact hm_max y hy_mem' hy_p
      · have h_res : listMaxOf (p := p) (x :: xs) = none := by
          simp [listMaxOf, hx, hm_none]
        rw [h_res]
        right
        refine ⟨rfl, ?_⟩
        intro y hy_mem hy_p
        cases hy_mem with
        | head _ => exact hx hy_p
        | tail _ hy_mem' => exact hm_all y hy_mem' hy_p

/-! ### `maxByElem` — element with maximum measure via `foldl`

`maxByElem f a as` folds over `as` with initial candidate `a`, keeping the element
that maximizes `f`. When `f` values tie, the earlier element is kept.
Unlike `maxBy` (which returns the maximum `Nat` value) or `maxVal` (which also
returns the value), `maxByElem` returns the *element* that achieves the maximum —
this is the "argmax" pattern, analogous to `maxByWeight` but using `≥` comparison
and `foldl`-based implementation. -/

/-- Returns the element with the largest measure `f` among `a` and the elements of `as`.
When measure values tie, prefers the earlier element. -/
def maxByElem (f : α → Nat) (a : α) (as : List α) : α :=
  as.foldl (fun (acc : α) (x : α) => if f acc ≥ f x then acc else x) a

/-- The measure of the result of `maxByElem` is at least the measure of the initial element. -/
theorem maxByElem_ge_initial (f : α → Nat) (a : α) (as : List α) : f (maxByElem f a as) ≥ f a := by
  induction as generalizing a with
  | nil => simp [maxByElem]
  | cons b bs ih =>
    by_cases h_ab : f a ≥ f b
    · have h_max : maxByElem f a (b :: bs) = maxByElem f a bs := by simp [maxByElem, h_ab]
      rw [h_max]
      apply ih
    · have h_fa_le_fb : f a ≤ f b := by omega
      have h_max : maxByElem f a (b :: bs) = maxByElem f b bs := by simp [maxByElem, h_ab]
      rw [h_max]
      have h := ih b
      omega

/-! ### Minimum and maximum elements via `foldl` -/

/-- Return the minimum element of a list with respect to `<`, or `none` if empty.
Uses `foldl` with a strict comparison, keeping the first occurrence of the minimum. -/
def minPos {α : Type u} [LinearOrder α] (l : List α) : Option α :=
  match l with
  | []      => none
  | h :: t  => some (t.foldl (fun acc x => if x < acc then x else acc) h)


lemma minPos_nil {α : Type u} [LinearOrder α] : minPos ([] : List α) = none := by
  simp [minPos]


lemma minPos_singleton {α : Type u} [LinearOrder α] (x : α) : minPos [x] = some x := by
  simp [minPos]

/-! ### `maxPos` — maximum element via `foldl` (dual of `minPos`)

`maxPos` is the dual of `minPos`: it returns the maximum element of a list using
`foldl` with a strict comparison, keeping the first occurrence of the maximum.
Returns `none` for the empty list. -/

/-- Return the maximum element of a list with respect to `>`, or `none` if empty.
Uses `foldl` with a strict comparison, keeping the first occurrence of the maximum.
This is the dual of `minPos`. -/
def maxPos {α : Type} [LinearOrder α] (l : List α) : Option α :=
  match l with
  | []      => none
  | h :: t  => some (t.foldl (fun acc x => if x > acc then x else acc) h)


lemma maxPos_nil {α : Type} [LinearOrder α] : maxPos ([] : List α) = none := by
  simp [maxPos]


lemma maxPos_singleton {α : Type} [LinearOrder α] (x : α) : maxPos [x] = some x := by
  simp [maxPos]

/-! ### `maxOfNonempty` and `minOfNonempty` — max/min with nonemptiness proof

These defs compute the max/min of a nonempty list, returning `α` directly
(rather than `Option α`). They use `foldl` with `max`/`min`, starting from
the first element. This avoids needing a sentinel/default value — useful for
types like `Int` where `0` is not a natural lower/upper bound. -/

/-- Maximum element of a nonempty list. Uses `foldl max` with the first
element as the initial accumulator. Returns the maximum directly, without `Option`.
Useful when a sentinel/default value would be unnatural (e.g., `List Int`). -/
def maxOfNonempty {α : Type} [LinearOrder α] (xs : List α) (hne : xs ≠ []) : α :=
  xs.tail.foldl max (xs.head hne)

/-- Minimum element of a nonempty list. Uses `foldl min` with the first
element as the initial accumulator. Returns the minimum directly, without `Option`.
Dual of `maxOfNonempty`. -/
def minOfNonempty {α : Type} [LinearOrder α] (xs : List α) (hne : xs ≠ []) : α :=
  xs.tail.foldl min (xs.head hne)


lemma maxOfNonempty_cons {α : Type} [LinearOrder α] (x : α) (xs : List α) (hne : x :: xs ≠ []) :
    maxOfNonempty (x :: xs) hne = xs.foldl max x := rfl


lemma minOfNonempty_cons {α : Type} [LinearOrder α] (x : α) (xs : List α) (hne : x :: xs ≠ []) :
    minOfNonempty (x :: xs) hne = xs.foldl min x := rfl


lemma maxOfNonempty_singleton {α : Type} [LinearOrder α] (x : α) (hne : [x] ≠ []) :
    maxOfNonempty [x] hne = x := by
  simp [maxOfNonempty]


lemma minOfNonempty_singleton {α : Type} [LinearOrder α] (x : α) (hne : [x] ≠ []) :
    minOfNonempty [x] hne = x := by
  simp [minOfNonempty]

/-- The result of `maxOfNonempty` is an element of the list. -/
lemma maxOfNonempty_mem {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) :
    maxOfNonempty xs hne ∈ xs := by
  cases xs with
  | nil => contradiction
  | cons a xs => exact (foldl_max_mem_and_ge_all a xs).1

/-- The result of `minOfNonempty` is an element of the list. -/
lemma minOfNonempty_mem {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) :
    minOfNonempty xs hne ∈ xs := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    have h_eq : minOfNonempty (x :: xs') hne = xs'.foldl min x := by
      simp [minOfNonempty_cons x xs' hne]
    rw [h_eq]
    rcases foldl_min_eq_or_mem x xs' with (h | h)
    · rw [h]; exact by simp
    · exact List.mem_cons_of_mem _ h

/-- Every element of `xs` is ≤ the maximum of `xs`.
For the empty list the statement holds vacuously since `hne` rules it out. -/
lemma maxOfNonempty_ge_of_mem {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) {x : α} (hx : x ∈ xs) :
    x ≤ maxOfNonempty xs hne := by
  cases xs with
  | nil => contradiction
  | cons a xs => exact (foldl_max_mem_and_ge_all a xs).2 x hx

/-- Every element of `xs` is ≥ the minimum of `xs`.
For the empty list the statement holds vacuously since `hne` rules it out. -/
lemma minOfNonempty_le_of_mem {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) {x : α} (hx : x ∈ xs) :
    minOfNonempty xs hne ≤ x := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact foldMin_le_initial xs x
    · exact foldMin_le_member xs a x hx

/-- `maxOfNonempty` on a nonempty list is the same as `maxWithDefault default` for any default.
The default is irrelevant for nonempty lists. -/
lemma maxOfNonempty_eq_maxWithDefault {α : Type} [LinearOrder α] (xs : List α) (hne : xs ≠ []) (default : α) :
    maxOfNonempty xs hne = maxWithDefault default xs := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    simp [maxOfNonempty_cons x xs' hne, maxWithDefault]

/-- `minOfNonempty` on a nonempty list is the same as `minWithDefault default` for any default.
The default is irrelevant for nonempty lists. -/
lemma minOfNonempty_eq_minWithDefault {α : Type} [LinearOrder α] (xs : List α) (hne : xs ≠ []) (default : α) :
    minOfNonempty xs hne = minWithDefault default xs := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    simp [minOfNonempty_cons x xs' hne, minWithDefault]

/-! ### Connection between `minPos` / `maxPos` and `minOfNonempty` / `maxOfNonempty` -/

/-- The foldl using `(fun acc a => if a < acc then a else acc)` equals foldl using `min`.
Both compute the minimum of the initial accumulator and all list elements. -/
lemma foldl_lt_eq_foldl_min {α : Type} [LinearOrder α] (xs : List α) (x : α) :
    xs.foldl (fun acc a => if a < acc then a else acc) x = xs.foldl min x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [List.foldl]
    have h_eq : (if y < x then y else x) = min x y := by
      by_cases h : y < x
      · simp [h, min_eq_right (le_of_lt h)]
      · simp [h, min_eq_left (not_lt.mp h)]
    rw [h_eq]
    exact ih (min x y)

/-- The foldl using `(fun acc a => if a > acc then a else acc)` equals foldl using `max`.
Both compute the maximum of the initial accumulator and all list elements. -/
lemma foldl_gt_eq_foldl_max {α : Type} [LinearOrder α] (xs : List α) (x : α) :
    xs.foldl (fun acc a => if a > acc then a else acc) x = xs.foldl max x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [List.foldl]
    have h_eq : (if y > x then y else x) = max x y := by
      by_cases h : y > x
      · simp [h, max_eq_right (le_of_lt h)]
      · simp [h, max_eq_left (not_lt.mp h)]
    rw [h_eq]
    exact ih (max x y)

/-- For a nonempty list, `minPos xs` returns `some` of the minimum computed by `minOfNonempty`. -/
lemma minPos_eq_some_minOfNonempty {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) :
    minPos xs = some (minOfNonempty xs hne) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    simp [minPos, minOfNonempty_cons x xs' hne, foldl_lt_eq_foldl_min xs' x]

/-- For a nonempty list, `maxPos xs` returns `some` of the maximum computed by `maxOfNonempty`. -/
lemma maxPos_eq_some_maxOfNonempty {α : Type} [LinearOrder α] {xs : List α} (hne : xs ≠ []) :
    maxPos xs = some (maxOfNonempty xs hne) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    simp [maxPos, maxOfNonempty_cons x xs' hne, foldl_gt_eq_foldl_max xs' x]

/-! ### `listMaxBy` — foldl-based maximum of a projection

`listMaxBy f xs` computes the maximum of `f a` over `a ∈ xs` via `foldl`.
Returns `0` for the empty list.

This is the foldl-based counterpart of `maxVal` (recursive). The lemma
`listMaxBy_eq_maxVal` shows they are equal. -/

/-- Maximum of `f a` over `a ∈ xs`, computed via `foldl` with `Nat.max`.
Returns `0` for the empty list. This is the foldl-based dual of `maxVal`. -/
def listMaxBy {α : Type _} (f : α → Nat) (xs : List α) : Nat :=
  xs.foldl (fun m a => max m (f a)) 0

/-! ### Connection between `listMaxBy` (foldl) and `maxVal` (recursive) -/

/-- Folding `Nat.max` with projection `f` over `xs` starting from `n` equals
`max n (maxVal f xs)`. This is the key lemma connecting the foldl-based maximum
to the recursive `maxVal`. -/
lemma foldl_max_eq_maxVal {α : Type _} (f : α → Nat) (xs : List α) (n : Nat) :
    xs.foldl (fun m a => max m (f a)) n = max n (maxVal f xs) := by
  induction xs generalizing n with
  | nil => simp [maxVal]
  | cons a as ih =>
    simp [maxVal_cons, ih, Nat.max_assoc]

/-- `listMaxBy f xs = maxVal f xs`: the foldl-based maximum equals the recursive maximum.
This follows from `foldl_max_eq_maxVal` with `n = 0`, plus `Nat.zero_max`. -/
lemma listMaxBy_eq_maxVal {α : Type _} (f : α → Nat) (xs : List α) :
    listMaxBy f xs = maxVal f xs := by
  dsimp [listMaxBy]
  rw [foldl_max_eq_maxVal f xs 0, Nat.zero_max]

/-! ### `maxElementBy` — find element maximizing a projection (returns `Option`)

`maxElementBy f ls` returns `some c` where `c ∈ ls` and `f c` is maximal, or `none` if `ls` is empty.
This generalizes `maxPos` (identity comparison) to an arbitrary projection `f : α → β`
where `β` is any `LinearOrder`. The internal fold uses a step function that keeps the
element with larger `f`-value, with the earlier element winning ties.

The lemmas `foldl_argmax_mem` and `foldl_argmax_max` are properties of the internal
foldl step, stated generically so they can be reused for other argmax-by-projection patterns.
-/

section MaxBy

variable {α β : Type} [LinearOrder β]

/-- The result of `foldl` with the argmax step function `λ best c => if f c > f best then c else best`
always belongs to `x :: xs`. -/
lemma foldl_argmax_mem (xs : List α) (f : α → β) (x : α) :
    (xs.foldl (fun (best : α) (c : α) => if f c > f best then c else best) x) ∈ x :: xs := by
  induction' xs with y ys ih generalizing x
  · exact List.mem_cons_self x []
  · rw [List.foldl_cons]
    by_cases hy : f y > f x
    · rw [if_pos hy]
      exact List.mem_cons_of_mem x (ih y)
    · rw [if_neg hy]
      have h := ih x
      rcases (List.mem_cons.mp h) with (h_eq | h_mem)
      · rw [h_eq]
        exact List.mem_cons_self x (y :: ys)
      · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y h_mem)

/-- The result of `foldl` with the argmax step function is a maximum element under `f`:
for any `c' ∈ x :: xs`, we have `f (foldl ...) ≥ f c'`. -/
lemma foldl_argmax_max (xs : List α) (f : α → β) (x : α) :
    ∀ c', c' ∈ x :: xs →
      f (xs.foldl (fun (best : α) (c : α) => if f c > f best then c else best) x) ≥ f c' := by
  induction' xs with y ys ih generalizing x
  · intro c' hc'
    rcases (List.mem_cons.mp hc') with (h_eq | hc'_rest)
    · rw [h_eq]; exact le_refl _
    · exact False.elim (by
        have := hc'_rest
        simp at this)
  · intro c' hc'
    rcases (List.mem_cons.mp hc') with (h_eq | hc'_rest)
    · rw [h_eq]
      rw [List.foldl_cons]
      by_cases hy : f y > f x
      · rw [if_pos hy]
        have h_ih : ∀ c'', c'' ∈ y :: ys →
          f (ys.foldl (fun (best : α) (c : α) => if f c > f best then c else best) y) ≥ f c'' := ih y
        have h_ih_y := h_ih y (by
          rw [List.mem_cons]
          exact Or.inl rfl)
        have hfyx : f y ≥ f x := le_of_lt hy
        exact le_trans hfyx h_ih_y
      · rw [if_neg hy]
        exact (ih x) x (by
          rw [List.mem_cons]
          exact Or.inl rfl)
    · rw [List.foldl_cons]
      by_cases hy : f y > f x
      · rw [if_pos hy]
        exact (ih y) c' hc'_rest
      · rw [if_neg hy]
        rcases (List.mem_cons.mp hc'_rest) with (h_eq2 | hc'_ys)
        · rw [h_eq2]
          have hfx_ge_foldl : f (ys.foldl (fun (best : α) (c : α) =>
              if f c > f best then c else best) x) ≥ f x := (ih x) x (by
            rw [List.mem_cons]
            exact Or.inl rfl)
          have hfx_ge_fy : f x ≥ f y := le_of_not_gt hy
          exact le_trans hfx_ge_fy hfx_ge_foldl
        · have hc'_xs : c' ∈ x :: ys := by
            rw [List.mem_cons]
            exact Or.inr hc'_ys
          exact (ih x) c' hc'_xs

/-- Find the element in `ls` with the maximum `f` value. Returns `none` if `ls` is empty.
This generalizes `maxPos` to an arbitrary projection `f : α → β` into any `LinearOrder β`. -/
def maxElementBy (ls : List α) (f : α → β) : Option α :=
  match ls with
  | [] => none
  | x :: xs =>
    some (xs.foldl (fun (best : α) (c : α) =>
      if f c > f best then c else best) x)

/-- `maxElementBy ls f` returns `none` iff `ls` is empty, otherwise returns `some c` where `c ∈ ls`
and `f c ≥ f c'` for all `c' ∈ ls`. This is the main correctness theorem for `maxElementBy`. -/
lemma maxElementBy_property (ls : List α) (f : α → β) :
    (maxElementBy ls f = none ∧ ls = []) ∨
    (∃ c, c ∈ ls ∧ maxElementBy ls f = some c ∧ ∀ c', c' ∈ ls → f c ≥ f c') := by
  cases ls with
  | nil =>
    left
    simp [maxElementBy]
  | cons x xs =>
    right
    let best : α := xs.foldl (fun (best : α) (c : α) => if f c > f best then c else best) x
    have hmem : best ∈ x :: xs := foldl_argmax_mem xs f x
    have hmax : ∀ c', c' ∈ x :: xs → f best ≥ f c' := foldl_argmax_max xs f x
    have h_eq : maxElementBy (x :: xs) f = some best := by
      simp [maxElementBy, best]
    exact ⟨best, hmem, h_eq, hmax⟩

end MaxBy

/-! ### `maxByFilter` — maximum element satisfying a predicate, with initial candidate

`maxByFilter p nums best` returns the maximum element in `{best} ∪ {x ∈ nums | p x}`.
In other words, it finds the greatest element among `best` and all elements of `nums`
that satisfy predicate `p`. When no element in `nums` beats `best` (either because
none satisfy `p` or all are `≤ best`), the result is `best`.

This generalizes `listMaxOf` (which returns `Option α`) to a setting where an explicit
initial candidate `best` serves as both the lower bound and the default.
-/

/-- Find the maximum among `best` and all elements of `nums` satisfying predicate `p`.
The result is `best` if no element in `nums` satisfies `p` and exceeds `best`.
When `p best` holds, the result is the maximum among `best` and `nums`-elements that
satisfy `p`. -/
def maxByFilter {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α) (best : α) : α :=
  match nums with
  | [] => best
  | x :: xs =>
    if p x then
      if x > best then maxByFilter p xs x else maxByFilter p xs best
    else
      maxByFilter p xs best
termination_by nums.length

/-- The result of `maxByFilter` is always at least `best`. -/
lemma maxByFilter_ge_best {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α) (best : α) :
    best ≤ maxByFilter p nums best := by
  induction' nums with x xs ih generalizing best
  · simp [maxByFilter]
  · simp only [maxByFilter]
    by_cases hx : p x = true
    · rw [if_pos hx]
      by_cases hlt : x > best
      · rw [if_pos hlt]
        have hxle : best ≤ x := le_of_lt hlt
        have hx_le_r : x ≤ maxByFilter p xs x := ih x
        exact le_trans hxle hx_le_r
      · rw [if_neg hlt]
        exact ih best
    · rw [if_neg hx]
      exact ih best

/-- Given `best = init ∨ p best = true`, the result either equals `init`
or satisfies `p`. This captures the invariant that we never "lose" the property
of either being the initial value or satisfying the predicate. -/
lemma maxByFilter_invariant {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α) (best : α)
    (init : α) (hbest : best = init ∨ p best = true) :
    maxByFilter p nums best = init ∨ p (maxByFilter p nums best) = true := by
  induction' nums with x xs ih generalizing best
  · simp [maxByFilter]
    rcases hbest with (h | h)
    · left; exact h
    · right; exact h
  · simp only [maxByFilter]
    by_cases hx : p x = true
    · rw [if_pos hx]
      by_cases hlt : x > best
      · rw [if_pos hlt]
        have hbest' : x = init ∨ p x = true := Or.inr hx
        exact ih x hbest'
      · rw [if_neg hlt]
        exact ih best hbest
    · rw [if_neg hx]
      exact ih best hbest

/-- The result of `maxByFilter` is either an element of `nums` or equals `best`. -/
lemma maxByFilter_mem_or_eq {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α) (best : α) :
    maxByFilter p nums best ∈ nums ∨ maxByFilter p nums best = best := by
  induction' nums with x xs ih generalizing best
  · simp [maxByFilter]
  · simp only [maxByFilter]
    by_cases hx : p x = true
    · rw [if_pos hx]
      by_cases hlt : x > best
      · rw [if_pos hlt]
        rcases ih x with (h | h)
        · left; exact List.mem_cons_of_mem x h
        · left; rw [h]; exact List.mem_cons_self x xs
      · rw [if_neg hlt]
        rcases ih best with (h | h)
        · left; exact List.mem_cons_of_mem x h
        · right; exact h
    · rw [if_neg hx]
      rcases ih best with (h | h)
      · left; exact List.mem_cons_of_mem x h
      · right; exact h

/-- For all `x ∈ nums` with `p x = true`, `x ≤ maxByFilter p nums best`.
Requires that `best` satisfies `best = init ∨ p best = true` for the induction. -/
lemma maxByFilter_is_largest {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α) (best : α)
    (init : α) (hbest : best = init ∨ p best = true) :
    ∀ x ∈ nums, p x = true → x ≤ maxByFilter p nums best := by
  induction' nums with x xs ih generalizing best
  · intro x hx; exact absurd hx (List.not_mem_nil _)
  · intro y hy hprime
    cases hy with
    | head _ =>
      simp only [maxByFilter]
      by_cases hx : p x = true
      · rw [if_pos hx]
        by_cases hlt : x > best
        · rw [if_pos hlt]
          exact maxByFilter_ge_best p xs x
        · rw [if_neg hlt]
          have hxle : x ≤ best := le_of_not_gt hlt
          have hbestle : best ≤ maxByFilter p xs best := maxByFilter_ge_best p xs best
          exact le_trans hxle hbestle
      · exact absurd hprime hx
    | tail _ hy' =>
      simp only [maxByFilter]
      by_cases hx : p x = true
      · rw [if_pos hx]
        by_cases hlt : x > best
        · rw [if_pos hlt]
          exact ih x (Or.inr hx) y hy' hprime
        · rw [if_neg hlt]
          exact ih best hbest y hy' hprime
      · rw [if_neg hx]
        exact ih best hbest y hy' hprime

/-- If no element in `nums` satisfies `p`, the result is `best`. -/
lemma maxByFilter_eq_best_of_any_false {α : Type} [LinearOrder α] (p : α → Bool) (nums : List α)
    (best : α) (h : List.any nums p = false) : maxByFilter p nums best = best := by
  induction' nums with x xs ih generalizing best
  · simp [maxByFilter]
  · have h_or : (p x || List.any xs p) = false := by simpa [List.any] using h
    have hx : p x = false := by
      cases hp : p x
      · rfl
      · simp [hp] at h_or
    have hxs : List.any xs p = false := by
      cases hany : List.any xs p
      · rfl
      · simp [hany] at h_or
    simp only [maxByFilter]
    have hx_not : ¬ p x = true := by simp [hx]
    rw [if_neg hx_not]
    exact ih best hxs

end List

namespace List

/-!
# `minWithRest` — extract the minimum element and the rest of a list

Given a list `l : List α` with a `LinearOrder α` instance,
`minWithRest l` returns `none` if `l` is empty, or `some (m, rest)` where
`m` is the minimum element of `l` and `rest` is `l` with one occurrence of `m` removed.

## `smallestSum` — sum of the `m` smallest elements

`smallestSum l m` repeatedly extracts the minimum element from `l` using
`minWithRest` and sums the first `m` such minima.

Performance note: both `minWithRest` and `smallestSum` are `O(n · m)` in the worst
case. They are intended for use in specifications and proofs, not in
performance-critical code.
-/

/-- Return the minimum element of a list together with the list
where this element has been removed.  If the list is empty,
return `none`.  Works for any linearly ordered type. -/
def minWithRest {α : Type} [LinearOrder α] (l : List α) : Option (α × List α) :=
  match l with
  | [] => none
  | x :: xs =>
    let rec go (curMin : α) (restAcc : List α) (remaining : List α) :
        α × List α :=
      match remaining with
      | [] => (curMin, restAcc)
      | y :: ys =>
        if y < curMin then
          go y (curMin :: restAcc) ys
        else
          go curMin (y :: restAcc) ys
    let (m, rest) := go x [] xs
    some (m, rest)

lemma minWithRest_eq_none_iff {α : Type} [LinearOrder α] {l : List α} :
    minWithRest l = none ↔ l = [] := by
  constructor
  · intro h
    cases l
    · rfl
    · rename_i x xs
      simp [minWithRest] at h
  · intro h; subst h; rfl

lemma minWithRest_ne_none_iff {α : Type} [LinearOrder α] {l : List α} :
    minWithRest l ≠ none ↔ l ≠ [] := by
  simpa using (minWithRest_eq_none_iff (l := l)).not

/-- Return the maximum element of a list together with the list
where one occurrence of this element has been removed.  If the list is empty,
return `none`.  Works for any linearly ordered type. -/
def maxWithRest {α : Type} [LinearOrder α] : List α → Option (α × List α)
  | [] => none
  | (x :: xs) =>
    match maxWithRest xs with
    | none => some (x, [])
    | some (m, rest) => if x > m then some (x, xs) else some (m, x :: rest)

lemma maxWithRest_eq_none_iff {α : Type} [LinearOrder α] {l : List α} :
    maxWithRest l = none ↔ l = [] := by
  constructor
  · intro h
    induction' l with x xs ih
    · rfl
    · unfold maxWithRest at h
      split at h
      · simp at h
      · rename_i m rest; split at h <;> simp at h
  · intro h; subst h; rfl

lemma maxWithRest_ne_none_iff {α : Type} [LinearOrder α] {l : List α} :
    maxWithRest l ≠ none ↔ l ≠ [] := by
  simpa using (maxWithRest_eq_none_iff (l := l)).not

/-- Sum of the `m` smallest elements of a list of natural numbers.
`smallestSum l 0 = 0`, and for `m > 0`, it picks the minimum element,
adds it to the sum, and recurses on the rest. -/
def smallestSum (l : List Nat) (m : Nat) : Nat :=
  match m with
  | 0 => 0
  | Nat.succ m' =>
    match minWithRest l with
    | none => 0
    | some (minVal, rest) => minVal + smallestSum rest m'


lemma smallestSum_zero (l : List Nat) : smallestSum l 0 = 0 := rfl

/-! ### `minDefault` — minimum value with a default for empty list -/

/-- Return the minimum element of a list, using `default` when the list is empty.
Works for any linearly ordered type. Unlike `minWithRest` (which returns an `Option`),
this always returns a value of the underlying type. -/
def minDefault {α : Type} [LinearOrder α] (default : α) : List α → α
  | [] => default
  | [x] => x
  | x :: xs => min x (minDefault default xs)

/-- `minDefault default l` is a lower bound for every element in `l`. -/
lemma minDefault_le_of_mem {α : Type} [LinearOrder α] (default : α) (l : List α) (a : α)
    (ha : a ∈ l) : minDefault default l ≤ a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp [List.mem_cons] at ha
    rcases ha with (rfl | ha)
    · match xs with
      | [] => simp [minDefault]
      | y :: ys => simpa [minDefault] using min_le_left x (minDefault default (y :: ys))
    · match xs with
      | [] => simp at ha
      | y :: ys =>
        simpa [minDefault] using le_trans (min_le_right x (minDefault default (y :: ys))) (ih ha)

/-- If the list is nonempty, then `minDefault default l` is in the list. -/
lemma minDefault_mem_of_ne_nil {α : Type} [LinearOrder α] (default : α) (l : List α)
    (h : l ≠ []) : minDefault default l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp [minDefault]
    | cons y ys =>
      have h_expand : minDefault default (x :: y :: ys) = min x (minDefault default (y :: ys)) := rfl
      rw [h_expand]
      by_cases hle : x ≤ minDefault default (y :: ys)
      · rw [min_eq_left hle]
        simp
      · have hlt : minDefault default (y :: ys) < x := lt_of_not_ge hle
        rw [min_eq_right (le_of_lt hlt)]
        have hne_nil : y :: ys ≠ [] := by simp
        have hmem := ih hne_nil
        exact List.mem_cons_of_mem _ hmem

end List

namespace List

/-! ### Minimum `some` in a list of `Option α` -/

/-- Find the minimum `some` value in a list of `Option α`.
    `none` entries are skipped; returns `none` if all entries are `none`. -/
def minOptionInList {α : Type} [LinearOrder α] : List (Option α) → Option α
  | [] => none
  | none :: rest => minOptionInList rest
  | some a :: rest =>
    match minOptionInList rest with
    | none => some a
    | some b => some (min a b)

/-- `minOptionInList` of an empty list is `none`. -/

lemma minOptionInList_nil {α : Type} [LinearOrder α] : minOptionInList ([] : List (Option α)) = none := by
  simp [minOptionInList]

/-- `minOptionInList` of a single `some a` is `some a`. -/

lemma minOptionInList_singleton_some {α : Type} [LinearOrder α] (a : α) :
    minOptionInList [some a] = some a := by
  simp [minOptionInList]

/-- If all entries in a list are `none`, `minOptionInList` returns `none`. -/
lemma minOptionInList_all_none {α : Type} [LinearOrder α] (l : List (Option α))
    (h : ∀ o ∈ l, o = none) : minOptionInList l = none := by
  first
  | (solve
    | rfl
    | simp_all [minOptionInList]
    | omega
    | aesop
    | simp_all [minOptionInList, List.foldl, List.foldr]
    | simp_all [minOptionInList, Nat.absDiff]
    | induction l <;> simp_all [minOptionInList]
    | cases l <;> simp_all [minOptionInList])


end List

namespace List

/-! ### `takeWhile` length bound -/

/-- The length of `List.takeWhile p l` is bounded above by the length of `l`. -/
lemma length_takeWhile_le {α : Type} (l : List α) (p : α → Bool) :
    (l.takeWhile p).length ≤ l.length := by
  rw [List.takeWhile_eq_take_findIdx_not]
  exact List.length_take_le' _ _

/-! ### `takeWhile` decomposition by first occurrence of an element

These lemmas describe how to split a list at the first occurrence of a specific element
using `takeWhile (· != a)` (prefix before `a`) and `dropWhile (· != a)` (suffix starting at `a`).
-/

/-- If `a ∈ l`, then `l` can be decomposed as the prefix of elements before the first `a`,
followed by `a`, followed by the suffix after `a`. -/
lemma takeWhile_decomp_of_mem {α : Type u} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    List.takeWhile (· != a) l ++ [a] ++ List.drop 1 (List.dropWhile (· != a) l) = l := by
  induction' l with x xs ih
  · simp at h
  · rw [List.mem_cons] at h
    rcases h with (rfl | h_mem)
    · simp
    · by_cases hx_eq : x = a
      · subst hx_eq
        simp
      · have hx_ne : (x != a) = true := by
          simp [hx_eq]
        calc
          List.takeWhile (· != a) (x :: xs) ++ [a] ++
              List.drop 1 (List.dropWhile (· != a) (x :: xs)) =
              (x :: List.takeWhile (· != a) xs) ++ [a] ++
              List.drop 1 (List.dropWhile (· != a) xs) := by
            simp [hx_ne]
          _ = x :: (List.takeWhile (· != a) xs ++ [a] ++
              List.drop 1 (List.dropWhile (· != a) xs)) := by
            simp
          _ = x :: xs := by rw [ih h_mem]

/-- The element `a` never appears in the `takeWhile (· != a)` prefix of any list.
This is a direct consequence of the definition of `takeWhile`: it only retains elements
that satisfy the predicate `(· != a)`. -/
lemma not_mem_takeWhile_ne {α : Type u} [DecidableEq α] {l : List α} {a : α} :
    a ∉ List.takeWhile (· != a) l := by
  intro hmem
  simpa using List.mem_takeWhile_imp hmem

/-! ### Filter length bound on drop-take slices -/

/-- The length of a filtered sublist (drop-take slice) is bounded by the take length.
For any list `l`, predicate `p`, and naturals `k` `n`:
`(((l.drop k).take n).filter p).length ≤ n`. -/
lemma length_filter_drop_take_le {α : Type _} (l : List α) (p : α → Bool) (k n : Nat) :
    (((l.drop k).take n).filter p).length ≤ n := by
  calc
    (((l.drop k).take n).filter p).length ≤ ((l.drop k).take n).length := List.length_filter_le _ _
    _ ≤ n := List.length_take_le _ _

/-! ### Prefix minimum (running minimum of a list) -/

/-- Accumulator for `prefixMin`: `prefixMinAux cur rest` returns the running
minima of `rest`, starting from the initial value `cur`. -/
def prefixMinAux {α : Type _} [Min α] (cur : α) : List α → List α
  | [] => []
  | y :: ys => let m := min cur y; m :: prefixMinAux m ys

/-- Prefix minimum of a list, generalized over any type with `Min`.
`prefixMin [a₁, a₂, …, aₙ] = [a₁, a₁⊓a₂, a₁⊓a₂⊓a₃, …, a₁⊓…⊓aₙ]`. -/
def prefixMin {α : Type _} [Min α] : List α → List α
  | [] => []
  | x :: xs => x :: prefixMinAux x xs

theorem prefixMin_nil {α : Type _} [Min α] : prefixMin ([] : List α) = [] := rfl

theorem prefixMin_singleton {α : Type _} [Min α] (x : α) : prefixMin [x] = [x] := rfl

end List
