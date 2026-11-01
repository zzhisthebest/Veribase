import Mathlib
import general.List.IndexedAccess

namespace List

/-! ### `inAtLeastTwo` — element appears in at least two of three lists -/

/-- Check if `v` appears in at least two of the three given lists.
This is a common pattern in "two out of three" problems where we need
to find elements present in at least two of three input arrays. -/
def inAtLeastTwo {α : Type} [DecidableEq α] (v : α) (l1 l2 l3 : List α) : Bool :=
  let in1 := decide (v ∈ l1)
  let in2 := decide (v ∈ l2)
  let in3 := decide (v ∈ l3)
  (in1 && in2) || (in1 && in3) || (in2 && in3)

lemma inAtLeastTwo_iff {α : Type} [DecidableEq α] (v : α) (l1 l2 l3 : List α) :
    inAtLeastTwo v l1 l2 l3 = true ↔
    ((v ∈ l1 ∧ v ∈ l2) ∨ (v ∈ l1 ∧ v ∈ l3) ∨ (v ∈ l2 ∧ v ∈ l3)) := by
  unfold inAtLeastTwo
  simp only [decide_eq_true_iff, Bool.and_eq_true, Bool.or_eq_true]
  tauto

/-- Membership characterization of the filtered deduplicated concatenation:
`v` belongs to the elements of `(l1 ++ l2 ++ l3).dedup` that pass `inAtLeastTwo`
iff `v` appears in at least two of the three lists. -/
lemma mem_filter_dedup_inAtLeastTwo {α : Type} [DecidableEq α] (v : α) (l1 l2 l3 : List α) :
    v ∈ List.filter (fun w => inAtLeastTwo w l1 l2 l3) ((l1 ++ l2 ++ l3).dedup) ↔
    ((v ∈ l1 ∧ v ∈ l2) ∨ (v ∈ l1 ∧ v ∈ l3) ∨ (v ∈ l2 ∧ v ∈ l3)) := by
  simp [List.mem_filter, List.mem_dedup, List.mem_append, inAtLeastTwo_iff]
  tauto


/-! ### `dedup` then `filter` — general lemmas -/

/-- Filtering a deduplicated list preserves `Nodup`, for any `Bool`-valued predicate.
This is a frequently needed combination: dedup then filter always produces a nodup result. -/
lemma nodup_dedup_filter {α : Type} [DecidableEq α] (l : List α) (f : α → Bool) :
    ((l.dedup).filter f).Nodup :=
  List.Nodup.filter f (List.nodup_dedup l)

/-- Membership in a dedup-then-filter list is equivalent to membership in the original list
and the predicate holding. -/
lemma mem_dedup_filter {α : Type} [DecidableEq α] (x : α) (l : List α) (p : α → Bool) :
    (x ∈ ((l.dedup).filter p)) ↔ (x ∈ l ∧ p x = true) := by
  simp [List.mem_dedup, List.mem_filter]

/-- The filtered deduplicated concatenation of three lists has no duplicates.
This follows from the fact that `dedup` produces a nodup list and `filter` preserves nodup. -/
lemma nodup_filter_dedup_inAtLeastTwo {α : Type} [DecidableEq α] (l1 l2 l3 : List α) :
    (List.filter (fun v => inAtLeastTwo v l1 l2 l3) ((l1 ++ l2 ++ l3).dedup)).Nodup :=
  nodup_dedup_filter _ _


/-! ### `filter` then `dedup` — general lemmas

These lemmas are about `(l.filter p).dedup` (filter THEN dedup), which is the
opposite order of the `((l.dedup).filter p)` lemmas above.
Both orders are useful in different contexts. -/

/-- `(l.filter p).dedup` is `Nodup`. Trivial by `List.nodup_dedup`. -/
lemma nodup_filter_dedup [DecidableEq α] (l : List α) (p : α → Bool) :
    (l.filter p).dedup.Nodup :=
  List.nodup_dedup _

/-- `(l.filter p).dedup` is a sublist of `l`.
Combines `dedup_sublist` and `filter_sublist`. -/
lemma sublist_filter_dedup [DecidableEq α] (l : List α) (p : α → Bool) :
    (l.filter p).dedup.Sublist l :=
  (List.dedup_sublist (l.filter p)).trans (List.filter_sublist l)

/-- If `a ∈ (l.filter p).dedup`, then `p a = true`. -/
lemma mem_filter_dedup_imp [DecidableEq α] {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ (l.filter p).dedup) : p a = true :=
  ((List.mem_filter.mp ((List.dedup_subset _) h)).2)

/-- If `a ∈ l` and `p a = true`, then `a ∈ (l.filter p).dedup`. -/
lemma mem_filter_dedup_of_mem_and_pred [DecidableEq α] {l : List α} {p : α → Bool} {a : α}
    (hmem : a ∈ l) (hp : p a = true) : a ∈ (l.filter p).dedup :=
  List.subset_dedup _ (List.mem_filter.mpr ⟨hmem, hp⟩)

/-- Membership in `(l.filter p).dedup` (filter then dedup) is equivalent to membership
in `l` and the predicate `p` holding. This is the combined `↔` version of
`mem_filter_dedup_imp` and `mem_filter_dedup_of_mem_and_pred`. -/

lemma mem_filter_dedup_iff [DecidableEq α] {l : List α} {p : α → Bool} {a : α} :
    a ∈ (l.filter p).dedup ↔ (a ∈ l ∧ p a) := by
  simp

/-- Membership in `((l.filter p).filter q).dedup` (two consecutive filters then dedup)
is equivalent to membership in `l` and both predicates `p` and `q` holding.
Generalizes `mem_filter_dedup_iff` to two predicates. -/
lemma mem_filter_filter_dedup_iff [DecidableEq α] {l : List α} {p q : α → Bool} {a : α} :
    a ∈ ((l.filter p).filter q).dedup ↔ a ∈ l ∧ p a ∧ q a := by
  rw [mem_filter_dedup_iff (l := l.filter p) (p := q), List.mem_filter]
  constructor
  · rintro ⟨⟨hl, hp⟩, hq⟩; exact ⟨hl, hp, hq⟩
  · rintro ⟨hl, hp, hq⟩; exact ⟨⟨hl, hp⟩, hq⟩


/-! ### `hasCommonElement` — boolean check if two lists share any element

`hasCommonElement l₁ l₂` returns `true` when there exists an element present in both
`l₁` and `l₂`. This is the boolean "intersection nonempty" test, implemented as
`any` with `elem`, and is more general than `commonElementsDedup` when only a yes/no
answer is needed. -/

/-- Returns `true` if two lists have any common element (using `BEq` for comparison).
For example, `hasCommonElement [1,2,3] [3,4,5] = true`. -/
def hasCommonElement {α : Type} [BEq α] (l₁ l₂ : List α) : Bool :=
  l₁.any (fun a => l₂.elem a)

/-- `hasCommonElement l₁ l₂ = true` iff there is an element belonging to both lists. -/

lemma hasCommonElement_iff {α : Type} [BEq α] [LawfulBEq α] (l₁ l₂ : List α) :
    hasCommonElement l₁ l₂ = true ↔ ∃ a, a ∈ l₁ ∧ a ∈ l₂ := by
  unfold hasCommonElement
  simp [List.any_eq_true, List.elem_eq_mem, decide_eq_true_iff]


/-! ### `commonElementsDedup` — deduplicated intersection of two lists

`commonElementsDedup xs ys` returns the deduplicated list of elements that
belong to both `xs` and `ys`. This is the filter-then-dedup pipeline applied
to membership in `ys`, a common building block for set-like operations. -/

/-- The deduplicated list of elements present in both `xs` and `ys`. -/
def commonElementsDedup [DecidableEq α] (xs ys : List α) : List α :=
  (xs.filter (λ x => decide (x ∈ ys))).dedup

/-- `commonElementsDedup` always produces a `Nodup` list. This is a direct
consequence of `List.nodup_dedup`. -/

theorem nodup_commonElementsDedup [DecidableEq α] (xs ys : List α) :
    (commonElementsDedup xs ys).Nodup :=
  List.nodup_dedup _

/-- Membership in `commonElementsDedup xs ys` is equivalent to being in both `xs` and `ys`. -/
theorem mem_commonElementsDedup_iff [DecidableEq α] (xs ys : List α) (a : α) :
    a ∈ commonElementsDedup xs ys ↔ a ∈ xs ∧ a ∈ ys := by
  unfold commonElementsDedup
  rw [mem_filter_dedup_iff]
  simp

/-- After merge-sorting the deduplicated intersection of `xs` and `ys` with
any comparator `r`, membership is still equivalent to being in both `xs` and `ys`.
This combines `List.mem_mergeSort` with `mem_commonElementsDedup_iff`. -/

theorem mem_mergeSort_commonElementsDedup_iff [DecidableEq α] (r : α → α → Bool) (xs ys : List α) (a : α) :
    a ∈ (commonElementsDedup xs ys).mergeSort r ↔ a ∈ xs ∧ a ∈ ys := by
  simp [mem_commonElementsDedup_iff]


/-! ### `memNatBool` — boolean membership for `Nat` lists

A decidable membership test for `Nat` lists using `List.any`.
Unlike `decide (x ∈ xs)`, this avoids requiring `DecidableEq Nat` in contexts
where it's not automatically available (e.g., certain recursion patterns). -/

/-- Boolean membership test for `Nat` lists: returns `true` iff `x` appears in `xs`. -/
def memNatBool (x : Nat) (xs : List Nat) : Bool :=
  xs.any (fun y => decide (y = x))

/-- Simplification for `memNatBool` on a cons. -/
lemma memNatBool_cons (x y : Nat) (ys : List Nat) :
    memNatBool x (y :: ys) = (decide (y = x) || memNatBool x ys) := by
  simp [memNatBool, List.any_cons]

/-- `memNatBool` is equivalent to `List.Mem` (as a boolean). -/
lemma memNatBool_iff (x : Nat) (xs : List Nat) : memNatBool x xs = true ↔ x ∈ xs := by
  simp [memNatBool, List.any_eq_true, decide_eq_true_iff]

/-- Membership in a filtered list: `x ∈ filter p xs` iff `x ∈ xs` and `p x`. -/
lemma memNatBool_filter (x : Nat) (l : List Nat) (p : Nat → Bool) :
    memNatBool x (l.filter p) = (memNatBool x l && p x) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases hpy : p y
    · simp [hpy, memNatBool_cons, ih]
      by_cases hxy : y = x
      · subst hxy; simp [hpy]
      · simp [hxy]
    · simp [hpy, memNatBool_cons, ih]
      by_cases hxy : y = x
      · subst hxy; simp [hpy]
      · simp [hxy]

/-! ### `nodupNatBool` — boolean no-duplicates check for `Nat` lists -/

/-- Boolean check: does a `List Nat` have no duplicate elements?
Uses `memNatBool` for the membership check in the tail. -/
def nodupNatBool : List Nat → Bool
  | [] => true
  | x :: rs => (! memNatBool x rs) && nodupNatBool rs

private lemma memNatBool_succ_map (x : Nat) (l : List Nat) :
    memNatBool x.succ (l.map Nat.succ) = memNatBool x l := by
  simp [memNatBool, List.any_map, Function.comp,
    show ((fun (y : Nat) => decide (y = x.succ)) ∘ Nat.succ) =
      (fun y => decide (y = x)) by ext y; simp]

private lemma memNatBool_zero_map_succ (l : List Nat) : memNatBool 0 (l.map Nat.succ) = false := by
  simp [memNatBool, List.any_map]

private lemma nodupNatBool_map_succ (l : List Nat) : nodupNatBool (l.map Nat.succ) = nodupNatBool l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [nodupNatBool, memNatBool_succ_map, memNatBool_zero_map_succ, ih]

/-- `List.range n` has no duplicates (boolean version). -/
lemma nodupNatBool_range (n : Nat) : nodupNatBool (List.range n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp [nodupNatBool, memNatBool_zero_map_succ, nodupNatBool_map_succ, ih]

/-! ### `containsAllElems` — check if a list contains all elements from another list -/

/-- Check if every element of `elems` is present in `xs`, as a `Bool`.
`containsAllElems xs elems` reads as "xs contains all elements of elems".
For example, `containsAllElems ['a','b','c','d'] ['a','c'] = true`. -/
def containsAllElems {α : Type} [DecidableEq α] (xs : List α) (elems : List α) : Bool :=
  elems.all (fun e => decide (e ∈ xs))

/-- `decide` of a `∀ x ∈ l, x ∈ xs` proposition equals `List.all` of the corresponding `Bool` predicate.
This bridges the propositional membership with the boolean `List.all` combinator. -/
lemma decide_forall_mem_eq_list_all {α : Type} [DecidableEq α] (l xs : List α) :
    decide (∀ x ∈ l, x ∈ xs) = l.all (fun x => decide (x ∈ xs)) := by
  induction l with
  | nil => simp
  | cons x ls ih =>
    simp [List.all, ih]

/-! ### `all` with `elem` — boolean membership via `List.elem` -/

/-- A list where every element is in `valid` by `List.elem` is equivalent to
every element being a member of `valid`. This bridges `List.all` with `List.elem`
and propositional membership. -/
lemma all_elem_eq_true_iff {α : Type} [BEq α] [LawfulBEq α] (l : List α) (valid : List α) :
    (l.all (fun w => valid.elem w)) = true ↔ ∀ w, w ∈ l → w ∈ valid := by
  rw [List.all_eq_true]
  simp [List.elem_eq_mem, decide_eq_true_iff]

/-- Filtering `l1` by membership of each element in `l2` (via `List.elem`)
yields exactly the elements that are in both lists: `x ∈ l1.filter (λ y => l2.elem y)`
iff `x ∈ l1 ∧ x ∈ l2`. This is the `filter`-`elem` counterpart of `mem_commonElementsDedup_iff`
(which also involves `dedup`), and is a direct bridge between `List.mem_filter` and
`List.elem_iff`. Given the `simp` proof, this is useful as a rewrite lemma for the common
pattern of computing a list intersection via `filter` and `elem`. -/

theorem mem_filter_elem_iff {α : Type u} [BEq α] [LawfulBEq α] (l1 l2 : List α) (x : α) :
    x ∈ (l1.filter (λ y => l2.elem y)) ↔ (x ∈ l1 ∧ x ∈ l2) := by
  simp [List.mem_filter, List.elem_iff]

/-! ### `subSubset` — propositional subset via `List.Forall` -/

/-- `subSubset sub orig` means every element of `sub` is also in `orig`, expressed
using `List.Forall`. This is the `Prop` counterpart of `containsAllElems` and is
equivalent to `∀ e ∈ sub, e ∈ orig`. -/
def subSubset (sub orig : List α) : Prop :=
  sub.Forall (fun e => e ∈ orig)


lemma subSubset_nil (orig : List α) : subSubset [] orig := by
  simp [subSubset]

/-! ### `splitAtElem` — split list at an element occurrence -/

/-- If `x ∈ l`, then `l` can be written as `l' ++ [x] ++ r` for some
surrounding lists `l'` and `r`. This is the "split at element" lemma. -/
theorem splitAtElem {α : Type u} (x : α) (l : List α) (h : x ∈ l) : ∃ (l' r : List α), l = l' ++ [x] ++ r := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with (rfl | hx)
    · exact ⟨[], ys, rfl⟩
    · rcases ih hx with ⟨l', r', heq⟩
      exact ⟨y :: l', r', by simp [heq]⟩

/-! ### `headD` membership for non-empty lists -/


/-- If a list is non-empty, then `head!` is a member of the list.
Contrast with `headD_mem_of_ne_nil` which takes a default value;
`head!` uses `Inhabited`-provided default. -/
lemma mem_head!_of_ne_nil {α : Type u} [Inhabited α] {xs : List α} (hne : xs ≠ []) : xs.head! ∈ xs := by
  cases xs
  · contradiction
  · simp

/-- In a nonempty list, if an element is a member but not in the tail, it must be the head.
This is a structural lemma: the only way an element can be in a list but not in its tail
is if it equals the head element. -/
lemma eq_head_of_mem_not_mem_tail {α : Type} {x : α} {l : List α} (hne : l ≠ []) (hx : x ∈ l) (hxt : x ∉ l.tail) :
    x = l.head hne := by
  have h_cons : l = l.head hne :: l.tail := (List.head_cons_tail l hne).symm
  rw [h_cons] at hx
  rcases (List.mem_cons (a := x) (b := l.head hne) (l := l.tail)).mp hx with (h | h)
  · exact h
  · exfalso; exact hxt h

/-! ### `getElem?` returns `some` implies membership -/

/-- If `l[i]?` returns `some a`, then `a` is in `l`.
This bridges the optional indexing operation to propositional membership. -/
lemma getElem?_some_mem {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  rw [List.mem_iff_getElem?]
  exact ⟨i, h⟩

/-! ### `Forall` membership lemma

`forall_mem_of_forall` bridges `List.Forall P l` (an inductive `Prop`) to
propositional membership `x ∈ l → P x`. This is the fundamental elimination
lemma for `List.Forall` in proofs. -/

/-- If `List.Forall P l` holds, then every element `x ∈ l` satisfies `P x`. -/
lemma forall_mem_of_forall {α : Type _} {P : α → Prop} {l : List α} (h : List.Forall P l) {x : α}
    (hx : x ∈ l) : P x := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp [List.Forall] at h
    rcases h with ⟨h_hd, h_tl⟩
    simp at hx
    rcases hx with (rfl | hx')
    · exact h_hd
    · exact ih h_tl hx'

/-! ### Singleton list membership -/

/-- All elements of a singleton list are equal to each other.
This is useful when a proof obligation requires showing that any two elements
drawn from `[x]` must be equal. -/

lemma singleton_all_eq {α : Type} {x : α} : ∀ a ∈ [x], ∀ b ∈ [x], a = b := by
  simp

/-! ### `mem_filter` with `decide` (Prop predicates)

These lemmas bridge `List.filter` with `decide` and `Prop`-valued predicates,
extending the basic `List.mem_filter` which works with `Bool`. -/

/-- If `x` is in `l.filter (λ a => decide (p a))`, then `p x` holds.
This extracts `Prop` evidence from membership in a `decide`-filtered list.
Unlike `List.mem_filter` which gives a `Bool` equality, this lemma directly
returns the `Prop`-valued condition. -/
lemma mem_of_mem_filter_decide {α : Type} {l : List α} {p : α → Prop} [DecidablePred p] {x : α}
    (h : x ∈ l.filter (λ a => decide (p a))) : p x := by
  rw [List.mem_filter] at h
  rcases h with ⟨_, hd⟩
  exact of_decide_eq_true hd

/-! ### `mem_filter` with boolean conjunction -/

/-- Membership in a list filtered by the conjunction of two boolean predicates:
`x ∈ L.filter (λ a => P a && Q a)` iff `x ∈ L`, `P x = true`, and `Q x = true`.
This combines `List.mem_filter` with `Bool.and_eq_true` into a single `iff`. -/

lemma mem_filter_bool_and {α : Type} {L : List α} {P Q : α → Bool} {x : α} :
    x ∈ L.filter (λ a => P a && Q a) ↔ x ∈ L ∧ P x = true ∧ Q x = true := by
  rw [List.mem_filter, Bool.and_eq_true]

/-! ### `mem_filter` with `Bool`/`Prop` predicate equivalence -/

/-- If a `Bool` predicate `p` and a `Prop` predicate `q` are pointwise equivalent
(`(p x : Prop) ↔ q x`), then membership in `List.filter p l` is equivalent to
membership in `l` and `q a`. This bridges `List.mem_filter` (which yields a `Bool`
coerced to `Prop`) to a pure `Prop`-valued condition.

For example, if `p` is `isAnagram w target` and `q a` is `anagramKey a = anagramKey target`,
then `a ∈ filter (isAnagram · target) words ↔ a ∈ words ∧ anagramKey a = anagramKey target`. -/
lemma mem_filter_iff_of_bool_equiv {l : List α} {p : α → Bool} {q : α → Prop}
    (h : ∀ x, (p x : Prop) ↔ q x) {a : α} : a ∈ List.filter p l ↔ a ∈ l ∧ q a := by
  rw [List.mem_filter]
  constructor
  · rintro ⟨hmem, hp⟩; exact ⟨hmem, (h a).mp hp⟩
  · rintro ⟨hmem, hq⟩; exact ⟨hmem, (h a).mpr hq⟩

/-! ### `mem_filter_not_mem` — filter excluding elements from another list -/

/-- Given a list `xs` and a list `as`, we have `n ∈ as.filter (λ x, !decide (x ∈ xs))`
iff `n ∈ as` and `n ∉ xs`. This is a common pattern when constructing the
difference of two lists or finding elements absent from a reference set. -/

theorem mem_filter_not_mem {α : Type} [DecidableEq α] {xs as : List α} {n : α} :
    n ∈ as.filter (fun x => !decide (x ∈ xs)) ↔ n ∈ as ∧ n ∉ xs := by
  rw [List.mem_filter]
  constructor
  · intro ⟨hn_as, hbnot⟩
    have hdec_false : decide (n ∈ xs) = false := by
      cases htest : decide (n ∈ xs) with
      | true => simp [htest] at hbnot
      | false => rfl
    have h_not_mem : n ∉ xs := of_decide_eq_false hdec_false
    exact ⟨hn_as, h_not_mem⟩
  · intro ⟨hn_as, h_not_mem⟩
    have hdec_false : decide (n ∈ xs) = false := decide_eq_false h_not_mem
    have hbnot : !decide (n ∈ xs) := by
      simp [hdec_false]
    exact ⟨hn_as, hbnot⟩

/-! ### `any` with boolean conjunction -/

/-- `(l.any (λ x => f x && g x) = true)` is equivalent to the existence of an
`x ∈ l` such that both `f x` and `g x` are `true`.  This unfolds `List.any_eq_true`
and `Bool.and_eq_true` in one step, giving a clean propositional form that is
easy to use in postcondition proofs. -/

lemma any_and_eq_true_iff {α : Type} (l : List α) (f g : α → Bool) :
    (l.any (λ x => f x && g x) = true) ↔ (∃ x, x ∈ l ∧ f x = true ∧ g x = true) := by
  rw [List.any_eq_true]
  simp [Bool.and_eq_true]

/-! ### `getElem` of filtered list satisfies the filter predicate -/

/-- If `i` is a valid index into `List.filter p xs`, then the element at that index
satisfies `p`. This is the `getElem` version of `mem_filter_imp`. -/
lemma getElem_filter_pred {α : Type} (p : α → Bool) (xs : List α) (i : Nat)
    (h : i < (xs.filter p).length) : p ((xs.filter p)[i]) = true :=
  (List.mem_filter.mp (List.getElem_mem h)).right

/-! ### `all` of filtered list satisfies the filter predicate -/

/-- If an element belongs to `List.filter p l`, then it satisfies `p`.
This is the `Prop`-based forward direction of `List.mem_filter`:
extracts the predicate evidence from filtered-list membership. -/
lemma mem_filter_imp {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : a ∈ l.filter p) : p a :=
  (List.mem_filter.mp h).2

/-- If `p a = true` implies `q a = true` for all `a`, then every element `x` in `l.filter p`
satisfies `q x = true`. This chains predicate implication through `filter`: when `p → q`
pointwise, membership in `filter p l` implies `q`. Generalizes `mem_filter_imp`. -/
lemma forall_mem_filter_of_imp {α : Type} {p q : α → Bool} {l : List α}
    (hpq : ∀ a, p a = true → q a = true) : ∀ x ∈ l.filter p, q x = true := by
  intro x hx
  rw [List.mem_filter] at hx
  rcases hx with ⟨_, hp⟩
  exact hpq x hp

/-- Every element of a filtered list satisfies the filter predicate.
This is the Boolean `List.all` version: `((l.filter p).all p) = true`.
For the `Prop` version, see `List.mem_filter` and `mem_filter_imp`. -/
lemma all_filter_eq_true {α : Type} (p : α → Bool) (l : List α) : ((l.filter p).all p) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_filter] at hx
  exact hx.2

/-- If a list is filtered by `f` and then reversed, every element in the result satisfies `f`.
This is the `∀ a ∈ …` version of `mem_filter_imp` combined with `mem_reverse`: reversing
does not affect the property that filtered elements satisfy the predicate. -/
lemma forall_mem_filter_reverse {α : Type u} (f : α → Bool) (xs : List α) :
    ∀ a ∈ (xs.filter f).reverse, f a := by
  intro a ha
  rw [List.mem_reverse] at ha
  rcases List.mem_filter.mp ha with ⟨_, haf⟩
  exact haf

/-- If `x` is in `l` filtered by the predicate `(· ≠ a)` (via `bne` / `!=`),
then `x ≠ a` as a proposition. This bridges `BEq`-based filter membership
to propositional inequality, using `bne_iff_ne` from `LawfulBEq`.
Common in problems that filter a list to exclude a specific element (e.g.,
"all elements except the maximum"). -/
theorem mem_filter_bne {α : Type u} {l : List α} {a x : α} [BEq α] [LawfulBEq α]
    (h : x ∈ l.filter (λ y => y != a)) : x ≠ a :=
  (bne_iff_ne (a := x) (b := a)).mp ((List.mem_filter.mp h).2)

/-! ### `membershipIndicator` — binary indicator vector for set membership

`membershipIndicator l s` returns a `List Nat` where the i-th element is `1` if
`l[i] ∈ s` and `0` otherwise. This is the binary vector representation of
which elements of `l` belong to `s`. -/

/-- Binary indicator vector: maps each element of `l` to `1` if it's in `s`, else `0`. -/
def membershipIndicator [DecidableEq α] (l : List α) (s : List α) : List Nat :=
  l.map (fun x => if x ∈ s then 1 else 0)


theorem length_membershipIndicator [DecidableEq α] (l s : List α) :
    (membershipIndicator l s).length = l.length := by
  simp [membershipIndicator]

theorem getElem_membershipIndicator [DecidableEq α] [Inhabited α] (l s : List α) (i : Nat)
    (hi : i < l.length) :
    (membershipIndicator l s)[i]! = if l[i]! ∈ s then 1 else 0 := by
  have hi_map : i < (membershipIndicator l s).length := by
    rw [length_membershipIndicator]
    exact hi
  simp [membershipIndicator, hi, hi_map, List.getElem_map]

/-! ### `dedup` → `map` membership lemmas

These lemmas describe the relationship between membership, `dedup`, and `map`.
They are commonly needed when proving properties of pipelines that first
deduplicate a list and then transform elements via a function. -/

/-- If an element is in a list, it is also in the deduplicated list.
This is the forward direction of `List.mem_dedup`. -/
lemma mem_of_mem_dedup {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : a ∈ l.dedup := by
  rw [List.mem_dedup]
  exact h

/-- If `a` is in `l`, then `f a` is in `(l.dedup).map f`. -/
lemma mem_map_of_mem_dedup {α : Type u} {β : Type v} [DecidableEq α]
    {a : α} {l : List α} {f : α → β} (h : a ∈ l) : f a ∈ (l.dedup).map f :=
  List.mem_map_of_mem f (mem_of_mem_dedup h)

/-- If `b` is in `(l.dedup).map f`, then there exists `a ∈ l` such that `b = f a`.
This is the converse direction: elements of the mapped-dedup list come from some
original element. -/
lemma exists_of_mem_map_dedup {α : Type u} {β : Type v} [DecidableEq α]
    {b : β} {l : List α} {f : α → β} (h : b ∈ (l.dedup).map f) : ∃ a, a ∈ l ∧ b = f a := by
  rcases List.mem_map.1 h with ⟨a, ha_dedup, hb_eq⟩
  rw [List.mem_dedup] at ha_dedup
  exact ⟨a, ha_dedup, hb_eq.symm⟩

/-! ### `dedup` → `map` with `(x, f x)` pair construction

When mapping `fun x => (x, f x)` over a deduplicated list, the first component
of any resulting pair must originate from the original list. This is useful for
key-value processing pipelines that deduplicate keys before computing values. -/

/-- If `(a, b)` is in the result of mapping `fun x => (x, f x)` over `xs.dedup`,
then `a ∈ xs`. This is the "key check": deduplicated keys all come from the input. -/
lemma fst_mem_of_mem_dedup_map_mkPair {α β : Type} [DecidableEq α] {f : α → β} {xs : List α}
    {a : α} {b : β} (h : (a, b) ∈ (xs.dedup).map (fun x => (x, f x))) : a ∈ xs := by
  rcases List.mem_map.mp h with ⟨x, hx, hx_eq⟩
  rcases Prod.mk.inj hx_eq with ⟨rfl, _⟩
  rw [List.mem_dedup] at hx
  exact hx

/-! ### `map` → `dedup` membership lemmas

These lemmas describe the relationship between membership, `map`, and `dedup`
when the *map* is applied first and *dedup* afterwards: `(l.map f).dedup`.
This is the dual of the `dedup` → `map` lemmas above, which work with `(l.dedup).map f`.

Both orders appear in practice; these lemmas cover the `map`-first case. -/

/-- If `x` is in list `l`, then `f x` is in the deduplicated mapped list `(l.map f).dedup`.
This is the `map` → `dedup` analog of `mem_map_of_mem_dedup`. -/
lemma mem_map_dedup_of_mem {α β : Type*} [DecidableEq β] {l : List α} {f : α → β} {x : α}
    (h : x ∈ l) : f x ∈ (l.map f).dedup :=
  List.mem_dedup.mpr (List.mem_map.mpr ⟨x, h, rfl⟩)

/-- If `y` is in the deduplicated mapped list `(l.map f).dedup`, there exists
a preimage `x ∈ l` such that `f x = y`.
This is the `map` → `dedup` analog of `exists_of_mem_map_dedup`. -/
lemma exists_of_mem_dedup_map {α β : Type*} [DecidableEq β] {l : List α} {f : α → β} {y : β}
    (h : y ∈ (l.map f).dedup) : ∃ x ∈ l, f x = y := by
  have h' : y ∈ l.map f := List.mem_dedup.mp h
  rcases List.mem_map.mp h' with ⟨x, hx, heq⟩
  exact ⟨x, hx, heq⟩

/-- A combined `↔` version combining `mem_map_dedup_of_mem` and `exists_of_mem_dedup_map`.
`b` is in the deduplicated mapped list `(l.map f).dedup` iff there exists `a ∈ l` with `f a = b`. -/
lemma mem_dedup_map_iff {α β : Type*} [DecidableEq β] {l : List α} {f : α → β} {b : β} :
    b ∈ ((l.map f).dedup : List β) ↔ ∃ a, a ∈ l ∧ f a = b := by
  constructor
  · exact exists_of_mem_dedup_map
  · intro ⟨a, ha, heq⟩
    rw [← heq]
    exact mem_map_dedup_of_mem ha

/-! ### `pwFilter` membership

`pwFilter R l` retains only those elements that satisfy `R` with all later kept elements.
The following lemma states that every element of `pwFilter R l` is also in `l`. -/

/-- If `a` is in `List.pwFilter R l`, then `a` is in `l`.
This is the fundamental membership property of the pairwise filter. -/
lemma mem_pwFilter {α : Type} {R : α → α → Prop} [DecidableRel R] {a : α} {l : List α}
    (h : a ∈ List.pwFilter R l) : a ∈ l := by
  induction l generalizing a with
  | nil => simp [List.pwFilter] at h
  | cons x xs ih =>
    have h_cons : List.pwFilter R (x :: xs) =
        if ∀ y ∈ List.pwFilter R xs, R x y then x :: List.pwFilter R xs else List.pwFilter R xs := by
      calc
        List.pwFilter R (x :: xs) =
          List.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) [] (x :: xs) := rfl
        _ = (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) x
              (List.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) [] xs) := rfl
        _ = (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) x (List.pwFilter R xs) := rfl
        _ = if ∀ y ∈ List.pwFilter R xs, R x y then x :: List.pwFilter R xs else List.pwFilter R xs := rfl
    rw [h_cons] at h
    by_cases hcond : ∀ y ∈ List.pwFilter R xs, R x y
    · rw [if_pos hcond] at h
      simp at h
      rcases h with (rfl | h')
      · exact .head _
      · exact .tail _ (ih h')
    · rw [if_neg hcond] at h
      exact .tail _ (ih h)

/-- If `a` is in `l.eraseDup`, then `a` is in `l`.
`eraseDup` is defined as `pwFilter (· != ·)`, so this follows from `mem_pwFilter`. -/
lemma mem_eraseDup {α : Type} [BEq α] [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l.eraseDup) : a ∈ l :=
  mem_pwFilter h

/-! ### `forall_mem_append_singleton` — forall over an appended singleton -/

/-- If a predicate `P` holds for every element of `xs` and also for `x`,
then it holds for every element of `xs ++ [x]`. -/
lemma forall_mem_append_singleton {α : Type} {xs : List α} {x : α}
    {P : α → Prop} (hxs : ∀ y ∈ xs, P y) (hx : P x) :
    ∀ y ∈ xs ++ [x], P y := by
  intro y hy
  rcases List.mem_append.mp hy with (hy' | hy'')
  · exact hxs y hy'
  · rcases List.mem_singleton.mp hy'' with rfl
    exact hx

/-! ### `empty_list_of_never` — empty list as result when predicate is never true

This lemma is useful for proving postconditions of the form
"result contains exactly the elements satisfying P", where the
result is `[]` and nothing satisfies `P` (i.e., `∀ x, ¬ P x`). -/

/-- If a predicate `P` is false for all inputs, then the empty list satisfies
the conjunction `(∀ x, x ∈ [] → P x) ∧ (∀ x, P x → x ∈ [])`.
This is a reusable lemma for postconditions of the form
"result contains exactly the elements satisfying P". -/
lemma empty_list_of_never {α : Type u} {P : α → Prop} (hP : ∀ x, ¬ P x) :
    (∀ x, x ∈ ([] : List α) → P x) ∧ (∀ x, P x → x ∈ ([] : List α)) := by
  constructor
  · intro x hx
    exfalso; exact List.not_mem_nil x hx
  · intro x hx
    exfalso; exact hP x hx

/-! ### `mem_of_filter_eq_cons` — head of non-empty filter is in the original list and satisfies the predicate

If `l.filter p = a :: rest`, then `a ∈ l` and `p a`. This is a structural lemma
for reasoning about the result of `filter` when it yields at least one element:
the first element `a` must have been in `l` and must satisfy `p`. -/

/-- If filtering a list yields a non-empty cons, the head is in the original list
and satisfies the filter predicate. -/
lemma mem_of_filter_eq_cons {α : Type u} {p : α → Bool} {l : List α} {a : α} {rest : List α}
    (h : l.filter p = a :: rest) : a ∈ l ∧ p a := by
  have ha : a ∈ l.filter p := by
    rw [h]
    simp
  exact List.mem_filter.mp ha

/-! ### `forall_ne_of_not_mem` — non-membership implies inequality with all elements -/

/-- If `a` is not in `l`, then `a` is not equal to any element `b ∈ l`. -/
lemma forall_ne_of_not_mem {α : Type} {a : α} {l : List α} (h : a ∉ l) : ∀ b ∈ l, a ≠ b := by
  intro b hb heq
  apply h
  rw [heq]
  exact hb

/-! ### `flatMap` then `dedup` — membership lemmas

These lemmas describe membership in `(xs.flatMap f).dedup` — the common pipeline of
concatenating `f`-images and then removing duplicates. -/

/-- If `a` is in the deduplicated flatMap, there exists an `x` in `xs` with `a ∈ f x`. -/
lemma mem_dedup_flatMap {α β : Type} [DecidableEq α] (f : β → List α) (xs : List β) (a : α)
    (h : a ∈ (xs.flatMap f).dedup) : ∃ x ∈ xs, a ∈ f x := by
  rw [List.mem_dedup, List.mem_flatMap] at h
  exact h

/-- If every `a` produced by `f x` for `x ∈ xs` satisfies `P a`, then every `a` in
    the deduplicated flatMap satisfies `P a`. -/
lemma forall_mem_dedup_flatMap {α β : Type} [DecidableEq α] (P : α → Prop)
    (f : β → List α) (xs : List β) (h : ∀ x ∈ xs, ∀ a ∈ f x, P a) :
    ∀ a ∈ (xs.flatMap f).dedup, P a := by
  intro a ha
  rw [List.mem_dedup, List.mem_flatMap] at ha
  rcases ha with ⟨x, hx, hax⟩
  exact h x hx a hax

end List

namespace List

/-! ### `memElem` — boolean membership test -/

/-- Boolean membership test: `memElem a l` returns `true` iff `a ∈ l`.
This is equivalent to `List.elem a l` from the standard library.
Defined via `any` and `decide` for convenient `simp` rewriting. -/
def memElem {α : Type} [DecidableEq α] (a : α) (l : List α) : Bool :=
  l.any (fun x => decide (x = a))


lemma memElem_nil {α : Type} [DecidableEq α] (a : α) : memElem a [] = false := by
  simp [memElem]

lemma memElem_cons {α : Type} [DecidableEq α] (a x : α) (xs : List α) :
    memElem a (x :: xs) = (decide (x = a) || memElem a xs) := by
  simp [memElem]

lemma memElem_iff {α : Type} [DecidableEq α] {a : α} {l : List α} :
    memElem a l = true ↔ a ∈ l := by
  simp [memElem, List.any_eq_true, decide_eq_true_iff]

/-! ### `List.elem` ⇔ membership -/

/-- If `a` is not in `as`, then `as.elem a` evaluates to `false`.
This is the complement of `List.elem_eq_true_of_mem` from the standard library. -/
lemma elem_eq_false_of_not_mem {α : Type} [DecidableEq α] {a : α} {as : List α} (h : a ∉ as) :
    as.elem a = false := by
  cases hval : as.elem a
  · rfl
  · exfalso
    have hmem : a ∈ as := (List.elem_iff (a := a) (as := as)).mp hval
    exact h hmem

/-! ### `List.map` and membership -/

/-- If no `a ∈ as` has `f a = b`, then `b` is not in the image of `as` under `f`.
Useful for reasoning about filtered maps and case-insensitive comparisons. -/
lemma not_mem_map_of_forall_ne {α β : Type} {f : α → β} {b : β} {as : List α}
    (h : ∀ a, a ∈ as → b ≠ f a) : b ∉ List.map f as := by
  intro hm
  rcases List.mem_map.mp hm with ⟨a, ha, heq⟩
  exact h a ha heq.symm

/-! ### `listSetEqual` — set-based equality on lists -/

/-- Decide whether two `List α` have the same set of elements (ignores multiplicity).
This is a boolean, decidable check: `listSetEqual l₁ l₂` is `true` iff
`l₁.toFinset = l₂.toFinset`. Useful for QuickCheck-style testable preconditions
where `List.Perm` (a `Prop`) would not be `Decidable`. -/
def listSetEqual {α : Type _} [DecidableEq α] (l₁ l₂ : List α) : Bool :=
  decide (l₁.toFinset = l₂.toFinset)

end List

namespace List

/-! ### `allDistinct` — pairwise distinct elements -/

/-- Check whether all elements in a list are pairwise distinct. -/
def allDistinct {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => if x ∈ xs then false else allDistinct xs

lemma allDistinct_nil {α : Type} [DecidableEq α] : allDistinct ([] : List α) = true := rfl

lemma allDistinct_singleton {α : Type} [DecidableEq α] (x : α) : allDistinct [x] = true := by
  simp [allDistinct]

lemma allDistinct_pair_of_ne {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y) : allDistinct [x, y] = true := by
  simp [allDistinct, h]

/-- `allDistinct l = true` iff `l` has no duplicate elements (`Nodup`).
This bridges the boolean decision procedure `allDistinct` with the propositional `List.Nodup`. -/
lemma allDistinct_eq_true_iff_nodup {α : Type} [DecidableEq α] (l : List α) :
    allDistinct l = true ↔ List.Nodup l := by
  constructor
  · induction l with
    | nil => intro; exact .nil
    | cons x xs ih =>
      intro h
      unfold allDistinct at h
      by_cases hmem : x ∈ xs
      · simp [hmem] at h
      · simp [hmem] at h
        exact .cons hmem (ih h)
  · intro h_nodup
    induction h_nodup with
    | nil => rfl
    | @cons a l' h_forall_ne _ ih =>
      unfold allDistinct
      have h_not_mem : a ∉ l' := by
        intro hmem
        exact h_forall_ne a hmem rfl
      simp [h_not_mem, ih]

/-- If a list has no duplicates, `allDistinct` returns `true`. -/
lemma allDistinct_eq_true_of_nodup {α : Type} [DecidableEq α] (l : List α) (h : l.Nodup) :
    allDistinct l = true :=
  (allDistinct_eq_true_iff_nodup l).mpr h

/-- `allDistinct` returns `false` iff the list has duplicates (`¬ Nodup`). -/
lemma allDistinct_eq_false_iff_not_nodup {α : Type} [DecidableEq α] (l : List α) :
    allDistinct l = false ↔ ¬ List.Nodup l := by
  rw [← allDistinct_eq_true_iff_nodup l, Bool.not_eq_true]

/-! ### `insertIfNew` — insert element if not already present -/

/-- Insert an element into a list only if it is not already present.
`insertIfNew acc w` returns `acc` unchanged if `w ∈ acc`, otherwise prepends `w`.

This is the step function for `foldl`-based deduplication: `dedupAll l = l.foldl insertIfNew []`.
Contrast with `List.insert` which always adds the element (producing duplicates). -/
def insertIfNew {α : Type} [DecidableEq α] (acc : List α) (w : α) : List α :=
  if w ∈ acc then acc else w :: acc

/-- A single `insertIfNew` step preserves `List.Nodup`. -/
lemma nodup_insertIfNew {α : Type} [DecidableEq α] (acc : List α) (w : α) (h : List.Nodup acc) :
    List.Nodup (insertIfNew acc w) := by
  unfold insertIfNew; split
  · exact h
  · exact h.cons (by assumption)

/-- Membership in `insertIfNew acc y` is equivalent to membership in `acc` or equality with `y`. -/
lemma mem_insertIfNew_iff {α : Type} [DecidableEq α] {x y : α} {acc : List α} :
    x ∈ insertIfNew acc y ↔ x ∈ acc ∨ x = y := by
  unfold insertIfNew
  by_cases hy : y ∈ acc
  · rw [if_pos hy]
    constructor
    · exact Or.inl
    · intro h; rcases h with (h | h)
      · exact h
      · subst h; exact hy
  · rw [if_neg hy]
    simp [or_comm]

/-- Folding `insertIfNew` over a list preserves `List.Nodup`.
This is the key lemma for proving that deduplication via `insertIfNew` produces nodup results. -/
lemma nodup_foldl_insertIfNew {α : Type} [DecidableEq α] (xs : List α) (acc : List α) (h : List.Nodup acc) :
    List.Nodup (xs.foldl insertIfNew acc) := by
  induction' xs with x xs ih generalizing acc
  · exact h
  · rw [List.foldl]
    apply ih
    exact nodup_insertIfNew acc x h

/-- Membership in a foldl over `insertIfNew` reduces to membership in `acc` or in the list. -/
lemma mem_foldl_insertIfNew_iff {α : Type} [DecidableEq α] {l : List α} {x : α} {acc : List α} :
    x ∈ l.foldl insertIfNew acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl, insertIfNew]
    by_cases hh : h ∈ acc
    · simp [hh, ih]
      constructor
      · rintro (hacc | hmem_t)
        · exact Or.inl hacc
        · exact Or.inr (Or.inr hmem_t)
      · rintro (hacc | (rfl | hmem_t))
        · exact Or.inl hacc
        · exact Or.inl hh
        · exact Or.inr hmem_t
    · simp [hh, ih]
      tauto

/-- The fold-step pattern (extract an optional value and conditionally insert) preserves `Nodup`.
This is the building block for proving that `foldl`-based pipelines which optionally produce
values and insert them into a nodup accumulator maintain the `Nodup` invariant. -/
lemma option_step_insertIfNew_nodup {α : Type} [DecidableEq α] (acc : List α) (h_nodup : acc.Nodup)
    (opt : Option α) :
    (match opt with
    | some x => insertIfNew acc x
    | none => acc).Nodup := by
  cases opt with
  | none => simp [h_nodup]
  | some x =>
    simp
    exact nodup_insertIfNew acc x h_nodup

/-- Folding over a list with a step that preserves `Nodup` yields a `Nodup` accumulator.
General version: any function `f : β → Option α` combined with `insertIfNew`.
This generalizes `nodup_foldl_insertIfNew` (which only folds `insertIfNew` directly over an `α` list)
to pipelines that first map elements to optional values via `f`. -/
lemma nodup_foldl_option_insertIfNew {α β : Type} [DecidableEq α] (f : β → Option α) (acc : List α)
    (h_nodup : acc.Nodup) (xs : List β) :
    (xs.foldl
      (fun (acc' : List α) (x : β) =>
        match f x with
        | some v => insertIfNew acc' v
        | none => acc')
      acc).Nodup := by
  induction' xs with h t ih generalizing acc
  · exact h_nodup
  · have h_step : (match f h with
      | some v => insertIfNew acc v
      | none => acc).Nodup := option_step_insertIfNew_nodup acc h_nodup (f h)
    rw [List.foldl]
    apply ih
    exact h_step

/-! ### `dedupAll` — remove all duplicates via membership check -/

/-- Remove all duplicate elements from a list, keeping the first occurrence of each element.
Uses a `foldl` with membership check, so the result is in reverse order of first appearance.
For example: `dedupAll [1,2,1,3] = [3,2,1]` (first occurrences: 1,2,3; reversed: 3,2,1).
Contrast with `List.dedup` which removes only consecutive duplicates, and
`List.eraseDup` which preserves original order. -/
def dedupAll [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) []

lemma dedupAll_nil [DecidableEq α] : dedupAll ([] : List α) = [] := by
  simp [dedupAll]

private lemma foldl_dedupAll_nonempty_init [DecidableEq α] (l init : List α) (hinit : init ≠ []) :
    (l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) init) ≠ [] := by
  induction' l with a as ih generalizing init
  · exact hinit
  · by_cases hmem : a ∈ init
    · simp [hmem]; exact ih init hinit
    · simp [hmem]; apply ih (a :: init); simp

/-- If the input list is nonempty, then `dedupAll l` is also nonempty. -/
lemma dedupAll_nonempty [DecidableEq α] {l : List α} (h : l ≠ []) : dedupAll l ≠ [] := by
  unfold dedupAll
  rcases l with ⟨⟩ | ⟨a, as⟩
  · exact absurd rfl h
  · simp; apply foldl_dedupAll_nonempty_init as [a]; simp

/-! ### `dedupAll` membership lemmas -/

/-- Auxiliary lemma: membership characterization for the foldl accumulator used in `dedupAll`.
`x` is in the result of folding "add if not present" over `xs` starting from `acc`
iff `x` was already in `acc` or `x` is in `xs`. -/
lemma foldl_dedupAll_mem_aux {α : Type} [DecidableEq α] (xs acc : List α) (x : α) :
    x ∈ (xs.foldl (fun a z => if z ∈ a then a else z :: a) acc) ↔ x ∈ acc ∨ x ∈ xs := by
  induction' xs with y ys ih generalizing acc x
  · simp
  · simp [List.foldl]
    rw [ih]
    by_cases hy : y ∈ acc
    · simp [hy]
      by_cases hxy : x = y
      · subst hxy; simp [hy]
      · simp [hxy]
    · simp [hy, or_comm, or_assoc, or_left_comm]

/-- `x ∈ dedupAll xs` iff `x ∈ xs`. Deduplication preserves the set of elements. -/
lemma mem_dedupAll {α : Type} [DecidableEq α] (xs : List α) (x : α) : x ∈ dedupAll xs ↔ x ∈ xs := by
  unfold dedupAll
  simp [foldl_dedupAll_mem_aux]

/-! ### `dedupAll` nodup lemmas -/

/-- Auxiliary lemma: the foldl accumulator in `dedupAll` preserves `Nodup`.
If `acc` is nodup, then the result of folding "add if not present" over `xs`
starting from `acc` is also nodup. -/
lemma foldl_dedupAll_nodup_aux {α : Type} [DecidableEq α] (xs acc : List α) (hacc : List.Nodup acc) :
    List.Nodup (xs.foldl (fun a z => if z ∈ a then a else z :: a) acc) := by
  induction' xs with y ys ih generalizing acc
  · exact hacc
  · simp [List.foldl]
    apply ih
    by_cases hy : y ∈ acc
    · simp [hy, hacc]
    · simp [hy, hacc]

/-- `dedupAll xs` has no duplicate elements. -/
lemma nodup_dedupAll {α : Type} [DecidableEq α] (xs : List α) : List.Nodup (dedupAll xs) := by
  unfold dedupAll
  apply foldl_dedupAll_nodup_aux xs [] (by simp)

/-! ### `uniq` — remove all duplicates, preserving first-occurrence order -/

/-- Remove all duplicate elements from a list, keeping the first occurrence of each element
and preserving the original order. Uses a `foldl` with `acc ++ [x]` to append new elements.

For example: `uniq [1,2,1,3] = [1,2,3]`.
Contrast with `dedupAll` which reverses the order (uses `x :: acc`), and `List.eraseDup`
which also preserves order but uses a different algorithm internally. -/
def uniq {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- Auxiliary lemma: if `y ∈ acc`, then `y` remains in the accumulator
after folding "add if not present" over `ys` with the `uniq` algorithm. -/
lemma foldl_uniq_preserves {α : Type} [DecidableEq α] (acc ys : List α) (y : α) (hy : y ∈ acc) :
    y ∈ ys.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc := by
  induction' ys with z zs ih generalizing acc
  · exact hy
  · apply ih
    by_cases hz : z ∈ acc
    · simpa [hz] using hy
    · have hmem : y ∈ acc ++ [z] := by
        simp [hy]
      simpa [hz] using hmem

/-- Auxiliary lemma: if `y ∈ ys`, then `y` ends up in the result of
folding "add if not present" over `ys` with the `uniq` algorithm. -/
lemma foldl_uniq_adds {α : Type} [DecidableEq α] (acc ys : List α) (y : α) (hy : y ∈ ys) :
    y ∈ ys.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc := by
  induction' ys with z zs ih generalizing acc
  · simp at hy
  · simp only [List.mem_cons] at hy
    rcases hy with (heq | hy')
    · rw [heq]
      by_cases hz : z ∈ acc
      · simpa [hz, List.foldl] using foldl_uniq_preserves acc zs z hz
      · have hz_in : z ∈ acc ++ [z] := by simp
        simpa [hz, List.foldl] using foldl_uniq_preserves (acc ++ [z]) zs z hz_in
    · simpa [List.foldl] using ih (if z ∈ acc then acc else acc ++ [z]) hy'

/-- `uniq xs` has no duplicate elements. -/
lemma nodup_uniq {α : Type} [DecidableEq α] (xs : List α) : (uniq xs).Nodup := by
  unfold uniq
  have h : ∀ (acc : List α), acc.Nodup →
      (xs.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc).Nodup := by
    intro acc hacc
    induction' xs with x xs ih generalizing acc
    · exact hacc
    · apply ih
      by_cases hx : x ∈ acc
      · simpa [hx] using hacc
      · have h_nodup_singleton : ([x] : List α).Nodup := by simp
        have h_disjoint : acc.Disjoint [x] := by
          rw [List.disjoint_singleton]
          exact hx
        have h_nodup_acc' : (acc ++ [x]).Nodup :=
          List.Nodup.append hacc h_nodup_singleton h_disjoint
        simpa [hx] using h_nodup_acc'
  exact h [] (by simp)

/-- If `c ∈ xs` then `c ∈ uniq xs`. Deduplication preserves membership. -/
lemma mem_uniq_of_mem {α : Type} [DecidableEq α] (xs : List α) (c : α) (hc : c ∈ xs) :
    c ∈ uniq xs := by
  unfold uniq
  exact foldl_uniq_adds [] xs c hc

/-- Auxiliary lemma: membership in the foldl accumulator used by `uniq`.
If `x` is in the result of folding "add if not present" over `l` starting from `acc`,
then `x` was already in `acc` or `x` is in `l`. -/
private lemma foldl_uniq_mem_aux {α : Type} [DecidableEq α] (l : List α) (acc : List α) (x : α) :
    x ∈ l.foldl (fun a z => if z ∈ a then a else a ++ [z]) acc → x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => intro h; exact Or.inl h
  | cons y ys ih =>
    rw [List.foldl]
    intro h
    by_cases hy : y ∈ acc
    · simp [hy] at h
      rcases ih acc h with (hx_acc | hx_ys)
      · exact Or.inl hx_acc
      · exact Or.inr (by simp [hx_ys])
    · simp [hy] at h
      -- h : x ∈ ys.foldl (fun a z => if z ∈ a then a else a ++ [z]) (acc ++ [y])
      rcases ih (acc ++ [y]) h with (hx_acc' | hx_ys)
      · -- x ∈ acc ++ [y]
        rw [List.mem_append] at hx_acc'
        rcases hx_acc' with (hx_acc | hx_sing)
        · exact Or.inl hx_acc
        · simp at hx_sing; subst hx_sing; exact Or.inr (by simp)
      · -- x ∈ ys
        exact Or.inr (by simp [hx_ys])

/-- `x ∈ uniq l` iff `x ∈ l`. Deduplication preserves the set of elements. -/
lemma mem_uniq_iff {α : Type} [DecidableEq α] (l : List α) (x : α) : x ∈ uniq l ↔ x ∈ l := by
  constructor
  · intro h
    unfold uniq at h
    rcases foldl_uniq_mem_aux l [] x h with (hx_nil | hx_l)
    · simp at hx_nil
    · exact hx_l
  · exact mem_uniq_of_mem l x

/-- `uniq l` is a permutation of `l.dedup` — the same set of elements, possibly in a different order. -/
lemma uniq_perm_dedup {α : Type} [DecidableEq α] (l : List α) : uniq l ~ l.dedup := by
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a ∈ l
  · have ha_uniq : a ∈ uniq l := (mem_uniq_iff l a).mpr ha
    have ha_dedup : a ∈ l.dedup := by
      rw [List.mem_dedup]
      exact ha
    rw [List.count_eq_one_of_mem (nodup_uniq l) ha_uniq,
      List.count_eq_one_of_mem (List.nodup_dedup l) ha_dedup]
  · have ha_not_uniq : a ∉ uniq l := by
      rw [mem_uniq_iff l a]
      exact ha
    have ha_not_dedup : a ∉ l.dedup := by
      rw [List.mem_dedup]
      exact ha
    rw [List.count_eq_zero_of_not_mem ha_not_uniq,
      List.count_eq_zero_of_not_mem ha_not_dedup]

/-- Sum of `List.count` over `uniq` equals the list length. -/
lemma sum_count_uniq_eq_length {α : Type} [DecidableEq α] (l : List α) :
    ((uniq l).map (fun c => List.count c l)).sum = l.length := by
  calc
    ((uniq l).map (fun c => List.count c l)).sum
        = ((l.dedup).map (fun c => List.count c l)).sum := by
      apply List.Perm.sum_eq
      apply List.Perm.map _ (uniq_perm_dedup l)
    _ = l.length := by rw [List.sum_map_count_dedup_eq_length]

/-! ### `uniqueElements` — remove all duplicates preserving first occurrence

`uniqueElements l` recursively removes duplicates from `l`, keeping the first
occurrence of each element. It uses `List.contains` on the tail to check whether
the head has already appeared, giving a structurally recursive algorithm that
preserves the original order.

Contrast with:
- `dedupAll` which uses `foldl` and reverses first-occurrence order
- `uniq` which uses `foldl` with `acc ++ [x]` preserving order
- `List.eraseDup` which uses `pwFilter` internally

Example: `uniqueElements [1, 2, 1, 3] = [1, 2, 3]`.
-/

/-- Remove all duplicates from a list, keeping the first occurrence of each element.
Uses structural recursion with `List.contains`. -/
def uniqueElements [DecidableEq α] (l : List α) : List α :=
  match l with
  | [] => []
  | x :: rest =>
    if rest.contains x then uniqueElements rest
    else x :: uniqueElements rest

/-- If `a` is in `l`, then `a` is in `uniqueElements l`. Deduplication preserves membership. -/
theorem uniqueElements_mem [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : a ∈ uniqueElements l := by
  induction' l with x rest ih generalizing a
  · simp at h
  · simp [uniqueElements]
    split
    · rename_i hx
      cases h with
      | head _ => exact ih hx
      | tail _ hmem => exact ih hmem
    · rename_i hx
      cases h with
      | head _ => exact List.mem_cons_self x (uniqueElements rest)
      | tail _ hmem => exact List.mem_cons_of_mem x (ih hmem)

/-- If `a` is in `uniqueElements l`, then `a` is in `l`. -/
theorem mem_of_uniqueElements_mem [DecidableEq α] {a : α} {l : List α} (h : a ∈ uniqueElements l) : a ∈ l := by
  induction' l with x rest ih generalizing a
  · simp [uniqueElements] at h
  · simp [uniqueElements] at h
    split at h
    · rename_i hx
      have hmem := ih h
      exact List.mem_cons_of_mem x hmem
    · rename_i hx
      cases h with
      | head _ => exact List.mem_cons_self x rest
      | tail _ hmem =>
        have hmem' := ih hmem
        exact List.mem_cons_of_mem x hmem'

/-- `uniqueElements l` has no duplicate elements. -/
theorem uniqueElements_nodup [DecidableEq α] (l : List α) : List.Nodup (uniqueElements l) := by
  induction' l with w rest ih
  · simp [uniqueElements]
  · simp [uniqueElements]
    split
    · rename_i hw
      exact ih
    · rename_i hw
      apply List.Nodup.cons
      · intro hmem
        have hmem' := mem_of_uniqueElements_mem hmem
        exact hw hmem'
      · exact ih

/-! ### `dedup_ne_nil_of_ne_nil` — dedup preserves non-emptiness -/

/-- `dedup` of a nonempty list is nonempty. `List.dedup` removes consecutive duplicates
and never produces an empty list from a nonempty input. -/
lemma dedup_ne_nil_of_ne_nil [DecidableEq α] {l : List α} (h : l ≠ []) : l.dedup ≠ [] := by
  cases l with
  | nil => contradiction
  | cons hd tl => simp

/-! ### `dedup_decide_nodup` — `decide` bridge for `List.nodup_dedup` -/

/-- A deduplicated list is nodup, expressed as a `decide` equality.
This bridges `List.nodup_dedup` to decidable propositions,
useful for postconditions that use `decide`. -/
lemma dedup_decide_nodup {α : Type} [DecidableEq α] (l : List α) :
    decide (l.dedup).Nodup = true :=
  decide_eq_true (List.nodup_dedup l)

/-! ### `nodup_dedup_and_mem_dedup` — `dedup` specification as a conjunction -/

/-- `dedup` produces a nodup list with exactly the same elements.
This combines `List.nodup_dedup` and `List.mem_dedup` into a single conjunction,
useful for postconditions of the form `result.Nodup ∧ (∀ x, x ∈ result ↔ x ∈ original)`. -/
theorem nodup_dedup_and_mem_dedup {α : Type} [DecidableEq α] (l : List α) :
    (l.dedup).Nodup ∧ (∀ a, a ∈ l.dedup ↔ a ∈ l) :=
  ⟨List.nodup_dedup l, λ _ => List.mem_dedup⟩

/-! ### `nodup_dedup_map` — mapping an injective function over `dedup` preserves nodup -/

/-- If `f` is injective, then mapping `f` over a deduplicated list preserves nodup.
This wraps `List.nodup_dedup l` (the dedup operation itself yields nodup) with
`List.Nodup.map` (injective `f` preserves nodup). -/
lemma nodup_dedup_map {α β : Type} [DecidableEq α] (f : α → β) (hf : Function.Injective f) (l : List α) :
    (l.dedup.map f).Nodup :=
  (List.nodup_dedup l).map hf

/-- `eraseDup` of the empty list is empty. -/

lemma eraseDup_nil [DecidableEq α] : (([] : List α).eraseDup) = [] := rfl

/-- `List.eraseDup` is idempotent: applying it twice is the same as applying it once.
Since `eraseDup` already removes all duplicates, a second pass has no effect. -/
theorem eraseDup_idempotent [BEq α] (xs : List α) :
    (xs.eraseDup).eraseDup = xs.eraseDup := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.eraseDup, ih]

/-! ### `pwFilter` and `eraseDup` non-emptiness -/

/-- `pwFilter R l` is nonempty if `l` is nonempty.
The `pwFilter` processes a list by keeping elements that are not related to any
preceding element already kept. A nonempty input always yields a nonempty output. -/
lemma pwFilter_nonempty {α : Type} (R : α → α → Prop) [DecidableRel R] (l : List α)
    (h : l ≠ []) : List.pwFilter R l ≠ [] := by
  induction l with
  | nil => exact absurd rfl h
  | cons hd tl ih =>
    unfold List.pwFilter
    simp
    split
    · simp
    · by_cases htl : tl = []
      · subst htl; simp at *
      · exact ih htl

/-- If a list is nonempty, then `eraseDup l` is nonempty.
Follows immediately from `pwFilter_nonempty` since `List.eraseDup` is defined as `pwFilter`. -/
lemma eraseDup_ne_nil_of_ne_nil {α : Type} [DecidableEq α] {l : List α} (h : l ≠ []) :
    l.eraseDup ≠ [] := by
  unfold List.eraseDup
  apply pwFilter_nonempty (fun x1 x2 => (x1 != x2) = true) l h

/-! ### `eraseDup` membership lemmas -/

/-- If `a` is not in `l`, then `a` is not in `l.eraseDup`.
This follows from the fact that `eraseDup l` is a subset of `l`. -/
lemma not_mem_eraseDup_of_not_mem {α : Type} [BEq α] {a : α} {l : List α} (h : a ∉ l) :
    a ∉ l.eraseDup := by
  intro hmem
  apply h
  have hsubset := List.pwFilter_subset (R := fun x1 x2 => (x1 != x2) = true) l
  exact hsubset hmem

/-- Recursion lemma for `eraseDup` on `x :: l`.
`(x :: l).eraseDup` is either `l.eraseDup` (if `x` already appears in `l.eraseDup`)
or `x :: l.eraseDup` (if `x` is new). -/
lemma eraseDup_cons_eq {α : Type} [DecidableEq α] (x : α) (l : List α) :
    (x :: l).eraseDup = if x ∈ l.eraseDup then l.eraseDup else x :: l.eraseDup := by
  have h_unfold : (x :: l).eraseDup =
      (if ∀ z ∈ l.eraseDup, (x != z) = true then x :: l.eraseDup else l.eraseDup) := by
    simp [List.eraseDup, List.pwFilter]
  rw [h_unfold]
  by_cases h : x ∈ l.eraseDup
  · have h_not : ¬ (∀ z ∈ l.eraseDup, (x != z) = true) := by
      intro hall
      have hmem := hall x h
      simp at hmem
    simp [h, h_not]
  · have h_forall : ∀ z ∈ l.eraseDup, (x != z) = true := by
      intro z hz
      have hne : z ≠ x := by
        intro heq; subst heq; exact h hz
      simp [hne.symm]
    simp [h, h_forall]

/-- `x ∈ l.eraseDup` iff `x ∈ l`. Erasing duplicates preserves the set of elements. -/
lemma mem_eraseDup_iff {α : Type} [DecidableEq α] (x : α) (l : List α) : x ∈ l.eraseDup ↔ x ∈ l := by
  induction l with
  | nil => simp [List.eraseDup]
  | cons h t ih =>
    rw [eraseDup_cons_eq h t]
    by_cases h_mem : h ∈ t.eraseDup
    · simp [h_mem]
      constructor
      · intro hx; right; exact ih.mp hx
      · intro hx; rcases hx with (rfl | hx)
        · exact h_mem
        · exact ih.mpr hx
    · simp [h_mem, ih]

/-- The `toFinset` of the deduplicated list equals the `toFinset` of the original list.
Erasing duplicates does not change the set of elements. -/
lemma toFinset_eraseDup_eq {α : Type} [DecidableEq α] (l : List α) :
    (l.eraseDup).toFinset = l.toFinset := by
  ext a
  simp [mem_eraseDup_iff]

/-! ### `filterDedup` — filter then remove duplicates -/

/-- Filter a list by a predicate, then remove duplicates, keeping first occurrences.
`filterDedup p l = (l.filter p).eraseDup`.
Useful for getting the unique elements satisfying `p` in first-occurrence order. -/
def filterDedup {α : Type} [BEq α] (p : α → Bool) (l : List α) : List α :=
  (l.filter p).eraseDup

/-! ### `filterMapDedup` — filter-map with deduplication -/

/-- Process a list with `f : α → Option β`, collecting distinct results into an accumulator.
Elements that map to `none` are skipped; elements that map to `some b` are added to the
accumulator only if `b` is not already present. The final result is the reversed accumulator,
so that the order of first occurrence is preserved.

`filterMapDedup f us acc = reverse (foldl insertIfNew (filterMap f us) (reverse acc))` -/
def filterMapDedup [DecidableEq β] (f : α → Option β) (us : List α) (acc : List β) : List β :=
  match us with
  | [] => acc.reverse
  | u :: us' =>
    match f u with
    | none => filterMapDedup f us' acc
    | some b =>
      if b ∈ acc then filterMapDedup f us' acc
      else filterMapDedup f us' (b :: acc)

/-- `filterMapDedup` preserves `Nodup`: if the accumulator is nodup,
then the result of `filterMapDedup f us acc` is also nodup. -/
lemma filterMapDedup_nodup [DecidableEq β] (f : α → Option β) (us : List α) (acc : List β)
    (hnd : List.Nodup acc) : List.Nodup (filterMapDedup f us acc) := by
  induction us generalizing acc with
  | nil =>
    simpa [filterMapDedup] using hnd
  | cons u us' ih =>
    simp [filterMapDedup]
    cases hfu : f u
    · simp
      exact ih acc hnd
    · rename_i b
      simp
      split
      · exact ih acc hnd
      · apply ih
        exact hnd.cons (by assumption)

/-! ### `countCommon` — count elements of one list present in another -/

/-- Count how many elements of `bs` are also in `as`.
This counts multiplicities in `bs`: each occurrence is counted separately.
For example, `countCommon [1,2,3] [2,3,5,2] = 3` (2 appears once, 3 appears once, 2 appears again). -/
def countCommon {α : Type} [DecidableEq α] (as bs : List α) : Nat :=
  (List.filter (fun x => x ∈ as) bs).length

lemma countCommon_nil_left {α : Type} [DecidableEq α] (bs : List α) :
    countCommon ([] : List α) bs = 0 := by
  simp [countCommon]

lemma countCommon_nil_right {α : Type} [DecidableEq α] (as : List α) :
    countCommon as [] = 0 := by
  simp [countCommon]

/-! ### `countCommonWithFreq` — count common elements with given occurrence frequencies -/

/-- Count elements that appear exactly `n` times in `xs` and exactly `m` times in `ys`.
Only elements present in the deduplicated union `(xs ++ ys).eraseDup` are considered,
so elements that don't appear in either list are not counted even if `n = 0` and `m = 0`.

For instance, `countCommonWithFreq xs ys 1 1` counts elements appearing exactly once
in both lists, which is the core of LeetCode 2085 "Count Common Words With One Occurrence". -/
def countCommonWithFreq {α : Type} [DecidableEq α] (xs ys : List α) (n m : Nat) : Nat :=
  ((xs ++ ys).eraseDup.filter (fun a => xs.count a = n ∧ ys.count a = m)).length

/-- `countCommonWithFreq` is symmetric: swapping the lists and swapping `n` with `m`
yields the same count. -/
lemma countCommonWithFreq_comm {α : Type} [DecidableEq α] (xs ys : List α) (n m : Nat) :
    countCommonWithFreq xs ys n m = countCommonWithFreq ys xs m n := by
  have nd (l : List α) : l.eraseDup.Nodup := by
    induction l with
    | nil => simp [List.eraseDup]
    | cons x xs ih => rw [eraseDup_cons_eq]; split <;> simp_all
  have hp : List.Perm (xs ++ ys).eraseDup (ys ++ xs).eraseDup := by
    apply (List.perm_ext_iff_of_nodup (nd _) (nd _)).mpr
    intro a
    simp [mem_eraseDup_iff, or_comm]
  unfold countCommonWithFreq
  have h := (hp.filter (fun a => decide (xs.count a = n ∧ ys.count a = m))).length_eq
  simpa [and_comm] using h

/-! ### `filterByCountGT` — filter elements by count threshold -/

/-- Given a list `l` and a natural number `n`, return the deduplicated list of
elements whose count in `l` exceeds `n`. -/
def filterByCountGT [DecidableEq α] (l : List α) (n : Nat) : List α :=
  (l.dedup).filter (fun x => decide (l.count x > n))

/-- If `x` is in `filterByCountGT l n`, then `l.count x > n`. -/
lemma mem_filterByCountGT {α : Type} [DecidableEq α] {l : List α} {n : Nat} {x : α}
    (h : x ∈ filterByCountGT l n) : l.count x > n := by
  unfold filterByCountGT at h
  rcases List.mem_filter.mp h with ⟨_, hx_dec⟩
  exact of_decide_eq_true hx_dec

/-- If `l.count x > n`, then `x` is in `filterByCountGT l n`. -/
lemma filterByCountGT_of_count_gt {α : Type} [DecidableEq α] {l : List α} {n : Nat} {x : α}
    (h : l.count x > n) : x ∈ filterByCountGT l n := by
  unfold filterByCountGT
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_dedup.mpr
    have hpos : 0 < l.count x := by omega
    exact (List.count_pos_iff.mp hpos)
  · exact decide_eq_true h

/-- `filterByCountGT l n` is `List.Nodup`. -/
lemma nodup_filterByCountGT {α : Type} [DecidableEq α] (l : List α) (n : Nat) :
    List.Nodup (filterByCountGT l n) := by
  unfold filterByCountGT
  apply List.Nodup.filter
  exact List.nodup_dedup l

/-! ### `allSame` — all elements are equal -/

/-- Check whether all elements in a list are equal.
Returns `true` for the empty list (vacuously true). -/
def allSame {α : Type} [DecidableEq α] (l : List α) : Bool :=
  match l with
  | [] => true
  | c :: cs => List.all cs (fun x => decide (x = c))


lemma allSame_nil {α : Type} [DecidableEq α] : allSame ([] : List α) = true := rfl

lemma allSame_singleton {α : Type} [DecidableEq α] (x : α) : allSame [x] = true := by
  simp [allSame]

/-! ### `countSubstringsWithDistinctElements` — count substrings where all elements are distinct -/

/-- Sliding-window loop helper: counts substrings of `xs` ending at positions
    up to `right` where all elements are distinct.  `lastPos` maps each
    element to its most recent index, and `left` is the left boundary of
    the current window.  `acc` accumulates the running total. -/
def countDistinctSubstringsLoop {α : Type u} [BEq α] [Hashable α] (xs : List α)
    (left right : Nat) (lastPos : Std.HashMap α Nat) (acc : Nat) : Nat :=
  if h : right < xs.length then
    let x := xs.get ⟨right, h⟩
    let prevPos := lastPos.get? x
    let newLeft := match prevPos with
      | some p => if p ≥ left then p + 1 else left
      | none => left
    let newLastPos := lastPos.insert x right
    countDistinctSubstringsLoop xs newLeft (right + 1) newLastPos (acc + (right - newLeft + 1))
  else
    acc
termination_by xs.length - right

/-- Count the number of substrings where all elements are mutually distinct.
    Uses a sliding window with `HashMap` to achieve O(n) time complexity
    on any type with `BEq` and `Hashable`. -/
def countSubstringsWithDistinctElements {α : Type u} [BEq α] [Hashable α] (xs : List α) : Nat :=
  countDistinctSubstringsLoop xs 0 0 (Std.HashMap.empty) 0

/-- Counting substrings of an empty list yields zero. -/
lemma countSubstringsWithDistinctElements_nil {α : Type u} [BEq α] [Hashable α] :
    countSubstringsWithDistinctElements ([] : List α) = 0 := by
  unfold countSubstringsWithDistinctElements countDistinctSubstringsLoop
  simp

/-! ### `nodup_map_filter_foldl_eq` — folding over mapped and filtered nodup list

Given a nodup list `uniq`, a function `f : α → Nat`, and an element `c : α`,
mapping each element to `(x, f x)`, filtering by `p.fst = c`, and summing `p.snd`
yields `f c` if `c` is in `uniq`, else `0`. This holds because nodup ensures
at most one pair matches the filter. -/

/-- On a nodup list, `map (x ↦ (x, f x))` then `filter (p.fst = c)` then `foldl (+) 0`
on the second components equals `f c` if `c ∈ uniq`, else `0`. -/
lemma nodup_map_filter_foldl_eq {α : Type} [DecidableEq α]
    (uniq : List α) (h_nodup : uniq.Nodup) (f : α → Nat) (c : α) :
    ((uniq.map (fun x => (x, f x))).filter (fun p => decide (p.fst = c))).foldl
      (fun (acc : Nat) (p : α × Nat) => acc + p.snd) 0 =
    if c ∈ uniq then f c else 0 := by
  induction uniq with
  | nil => simp
  | cons hd tl ih =>
    have h_notin_tl : hd ∉ tl := List.Nodup.not_mem h_nodup
    have h_nodup_tl : tl.Nodup := (List.nodup_cons.mp h_nodup).right
    by_cases h_eq : hd = c
    · subst h_eq
      have h_filter_nil : ((tl.map (fun x => (x, f x))).filter
          (fun p => decide (p.fst = hd))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
        have hne : x ≠ hd := by
          intro heq; subst heq; exact h_notin_tl hx
        simp [hne]
      simp [h_filter_nil]
    · rw [List.map_cons, List.filter_cons]
      have h_decide : decide ((hd, f hd).fst = c) = false := by simp [h_eq]
      have h_mem : (c ∈ hd :: tl) = (c ∈ tl) := by simp [Ne.symm h_eq]
      simp [h_decide, h_mem, ih h_nodup_tl]

/-! ### `eraseDupBy` / `eraseDupByAux` — remove duplicates by a key function -/

/-- Remove duplicates from a list `cs` by a key function `f`.
The first occurrence of each key is kept; subsequent occurrences are dropped.
`seen` tracks the keys already encountered. -/
def eraseDupByAux (f : α → β) [DecidableEq β] (cs : List α) (seen : List β) : List α :=
  match cs with
  | [] => []
  | c :: cs' =>
    if f c ∈ seen then
      eraseDupByAux f cs' seen
    else
      c :: eraseDupByAux f cs' (f c :: seen)

/-- Remove duplicates from a list `cs` by a key function `f`.
The first occurrence of each key is kept; subsequent occurrences are dropped.
This is the public wrapper around `eraseDupByAux`. -/
def eraseDupBy (f : α → β) [DecidableEq β] (cs : List α) : List α :=
  eraseDupByAux f cs []

lemma eraseDupByAux_sublist (f : α → β) [DecidableEq β] (cs : List α) (seen : List β) :
    (eraseDupByAux f cs seen).Sublist cs := by
  induction cs generalizing seen with
  | nil => simp [eraseDupByAux]
  | cons c cs' ih =>
    simp [eraseDupByAux]
    split
    · exact (ih seen).cons c
    · exact (ih (f c :: seen)).cons₂ c

/-! ### `distinctElems` — `BEq`-based distinctness check -/

/-- Check whether all elements in a list are pairwise distinct, using `BEq.elem`
for membership testing. This works for types with `BEq` but not necessarily
`DecidableEq`. When `DecidableEq` is available, see `allDistinct`. -/
def distinctElems {α : Type} [BEq α] : List α → Bool
  | [] => true
  | c :: rest => !(rest.elem c) && distinctElems rest

lemma distinctElems_nil {α : Type} [BEq α] : distinctElems ([] : List α) = true := rfl

lemma distinctElems_singleton {α : Type} [BEq α] (x : α) : distinctElems [x] = true := by
  simp [distinctElems]

/-- When `BEq` is lawful and `DecidableEq` is available, `distinctElems` is equivalent
to `List.Nodup`. This bridges the `BEq`-based decision procedure with the
`DecidableEq`-based `Prop`. -/
theorem distinctElems_iff_nodup {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (cs : List α) :
    distinctElems cs ↔ cs.Nodup := by
  constructor
  · intro h
    induction' cs with c cs ih
    · exact List.nodup_nil
    · have h_expand : (!(cs.elem c) && distinctElems cs) = true := h
      simp at h_expand
      rcases h_expand with ⟨h_elem_false, hrest⟩
      have h_nodup_cs : cs.Nodup := ih hrest
      exact List.Nodup.cons h_elem_false h_nodup_cs
  · intro h
    induction' h with c cs hnotmem h_nodup ih
    · rfl
    · unfold distinctElems
      have h_not_mem : c ∉ cs := fun hm => hnotmem c hm rfl
      have helem : cs.elem c = false := by
        rw [List.elem_eq_mem]
        simp [h_not_mem]
      rw [helem]
      simp [ih]

/-! ### `distinctSubListLengths` — contiguous sublist lengths with distinct elements -/

/-- All lengths of contiguous sublists of `xs` that consist of pairwise distinct elements.
Returns a `List Nat` where each entry `len` means there exists a contiguous sublist
`(xs.drop i).take len` with all elements distinct. -/
def distinctSubListLengths {α : Type} [BEq α] (xs : List α) : List Nat :=
  let n := xs.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i + 1)).filter (fun len =>
      distinctElems ((xs.drop i).take len)
    )
  )

/-- If a contiguous sublist has no duplicate elements and has positive length,
then its length belongs to `distinctSubListLengths`. -/
theorem mem_distinctSubListLengths_of_valid {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (xs : List α) (i len : Nat)
    (h_bound : i + len ≤ xs.length) (h_pos : 0 < len)
    (h_nodup : ((xs.drop i).take len).Nodup) :
    len ∈ distinctSubListLengths xs := by
  have hi_lt_n : i < xs.length := by
    by_contra! H
    have : i + len > xs.length := by
      have h_add : i + len ≥ xs.length + len := Nat.add_le_add_right H len
      omega
    omega
  have hi_range : i ∈ List.range (xs.length) := List.mem_range.mpr hi_lt_n
  have hlen_range : len ∈ List.range (xs.length - i + 1) := by
    apply List.mem_range.mpr
    omega
  have h_distinct : distinctElems ((xs.drop i).take len) :=
    (distinctElems_iff_nodup _).mpr h_nodup
  unfold distinctSubListLengths
  exact List.mem_flatMap.mpr ⟨i, hi_range, List.mem_filter.mpr ⟨hlen_range, h_distinct⟩⟩

/-! ### `nodup_getElem?_ne_getElem?` — elements at distinct indices differ -/

/-- In a nodup list, elements at distinct indices are distinct.
Extracts the `→` direction of `List.nodup_iff_getElem?_ne_getElem?`. -/
lemma nodup_getElem?_ne_getElem? {α : Type u} {l : List α} (h : l.Nodup) (i j : Nat)
    (hij : i < j) (hj : j < l.length) : l[i]? ≠ l[j]? :=
  (List.nodup_iff_getElem?_ne_getElem?.mp h) i j hij hj

/-! ### `nodup_of_take` — `Nodup` is preserved by `take` -/

/-- If a list has no duplicate elements, then any prefix (via `take n`) also has no duplicates.
This follows from `List.take_sublist n l` and `List.Sublist.nodup`. -/
theorem nodup_of_take {α : Type} {l : List α} (h : List.Nodup l) (n : Nat) :
    List.Nodup (l.take n) :=
  (List.take_sublist n l).nodup h

/-! ### `nodup_append_singleton` — appending a new element preserves Nodup -/

/-- Appending a singleton to a Nodup list preserves Nodup if the new element
is not already in the list. -/
lemma nodup_append_singleton {α : Type} {xs : List α} {x : α}
    (h_nodup : List.Nodup xs) (h_not_mem : x ∉ xs) :
    List.Nodup (xs ++ [x]) := by
  refine List.Nodup.append h_nodup (by simp) ?_
  intro y hy_mem hy_singleton
  rcases List.mem_singleton.mp hy_singleton with rfl
  exact h_not_mem hy_mem

/-! ### `removeAdjacentDups` — remove adjacent duplicates -/

/-- Remove adjacent duplicate elements from a list, keeping the first occurrence
of each consecutive run. For example: `removeAdjacentDups [1, 1, 2, 2, 1] = [1, 2, 1]`.
Contrast with `List.dedup` (which removes ALL duplicates via `pwFilter`, not just
adjacent ones) and `List.eraseDup` (removes all duplicates preserving first occurrence). -/
def removeAdjacentDups [DecidableEq α] : List α → List α
| [] => []
| [x] => [x]
| (x :: y :: rest) => if x = y then removeAdjacentDups (y :: rest) else x :: removeAdjacentDups (y :: rest)

/-- Membership is preserved by `removeAdjacentDups`:
`x ∈ removeAdjacentDups l ↔ x ∈ l`. -/
lemma mem_removeAdjacentDups [DecidableEq α] (x : α) (l : List α) :
    x ∈ removeAdjacentDups l ↔ x ∈ l := by
  induction l generalizing x with
  | nil => simp [removeAdjacentDups]
  | cons a l' ih =>
      cases l' with
      | nil => simp [removeAdjacentDups]
      | cons b l'' =>
          unfold removeAdjacentDups
          split
          · simp [ih, *]
          · simp [ih, *]

/-- If `l` is pairwise sorted by `(· ≤ ·)`, then `removeAdjacentDups l` is also
pairwise sorted by `(· ≤ ·)`. Removing adjacent duplicates preserves sortedness. -/
lemma pairwise_removeAdjacentDups [DecidableEq α] [LinearOrder α] (l : List α)
    (h : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· ≤ ·) (removeAdjacentDups l) := by
  induction h with
  | nil => simp [removeAdjacentDups]
  | cons h_all h_pairwise ih =>
      rename_i a l'
      cases l' with
      | nil => simp [removeAdjacentDups]
      | cons b l'' =>
          have ha_b : a ≤ b := h_all b (by simp)
          have h_all_l'' : ∀ a' ∈ l'', a ≤ a' := by
            intro a' ha'; apply h_all a'; simp [ha']
          have h_cons := (List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := l'')).mp h_pairwise
          rcases h_cons with ⟨h_all_b, h_pairwise_l''⟩
          unfold removeAdjacentDups
          by_cases heq : a = b
          · rw [if_pos heq]
            exact ih
          · rw [if_neg heq]
            have h_first : ∀ a' ∈ removeAdjacentDups (b :: l''), a ≤ a' := by
              intro a' ha'
              rw [mem_removeAdjacentDups] at ha'
              have ha'_cases := List.mem_cons.mp ha'
              rcases ha'_cases with (rfl | ha'_l'')
              · exact ha_b
              · exact h_all_l'' a' ha'_l''
            exact List.Pairwise.cons h_first ih

/-- If `l` is pairwise sorted by `(· ≤ ·)`, then `removeAdjacentDups l` has no duplicates.
This holds because in a sorted list, all equal elements are adjacent, so removing adjacent
duplicates eliminates all duplicates. -/
lemma nodup_removeAdjacentDups [DecidableEq α] [LinearOrder α] (l : List α)
    (h : List.Pairwise (· ≤ ·) l) :
    List.Nodup (removeAdjacentDups l) := by
  induction h with
  | nil => simp [removeAdjacentDups]
  | cons h_all h_pairwise ih =>
      rename_i a l'
      cases l' with
      | nil => simp [removeAdjacentDups]
      | cons b l'' =>
          have ha_b : a ≤ b := h_all b (by simp)
          have h_all_l'' : ∀ a' ∈ l'', a ≤ a' := by
            intro a' ha'; apply h_all a'; simp [ha']
          have h_cons := (List.pairwise_cons (R := (· ≤ ·)) (a := b) (l := l'')).mp h_pairwise
          rcases h_cons with ⟨h_all_b, h_pairwise_l''⟩
          unfold removeAdjacentDups
          by_cases heq : a = b
          · rw [if_pos heq]
            exact ih
          · rw [if_neg heq]
            rw [List.nodup_cons]
            refine And.intro ?_ ih
            rw [mem_removeAdjacentDups]
            intro ha_in
            have ha_in_cases := List.mem_cons.mp ha_in
            rcases ha_in_cases with (rfl | ha_in_l'')
            · exact heq rfl
            · have hba : b ≤ a := h_all_b a ha_in_l''
              exact heq (le_antisymm ha_b hba)

/-! ### `nodup_map_mk_self` — mapping `(a, f a)` preserves `Nodup` -/

/-- Mapping `(fun a => (a, f a))` preserves `Nodup`.
The function `a ↦ (a, f a)` is injective (since `Prod.fst` recovers `a`),
so a `Nodup` list remains `Nodup` under this map. -/
lemma nodup_map_mk_self {α β : Type} {l : List α} {f : α → β} (h_nodup : l.Nodup) :
    (l.map (fun a => (a, f a))).Nodup := by
  apply h_nodup.map
  intro a b h
  have := congrArg Prod.fst h
  simpa using this

/-! ### `distinctKeys` — unique keys from an association list -/

/-- Extract unique keys from an association list, preserving the order of first occurrence.
`distinctKeys [(a₁, b₁), (a₂, b₂), ...]` returns `[a₁, a₂, ...]` with duplicates removed.
Equivalent to `(xs.map Prod.fst).eraseDup`. -/
def distinctKeys {α β : Type} [DecidableEq α] (xs : List (α × β)) : List α :=
  (xs.map Prod.fst).eraseDup

/-- `distinctKeys` always produces a `Nodup` list, since `eraseDup` removes all duplicates. -/
lemma nodup_distinctKeys {α β : Type} [DecidableEq α] (xs : List (α × β)) :
    (distinctKeys xs).Nodup := by
  unfold distinctKeys
  have h_irrefl : IsIrrefl α (fun x y => (x != y) = true) := ⟨by intro a; simp⟩
  have h_pairwise : List.Pairwise (fun x y => (x != y) = true) ((xs.map Prod.fst).eraseDup) :=
    List.pairwise_pwFilter (R := fun x y => (x != y) = true) (xs.map Prod.fst)
  exact h_pairwise.nodup

end List

namespace List


/-! ### Distinct element count -/

/-- Count the number of distinct (unique) elements in a list.
Uses `toFinset` which deduplicates, then takes the cardinality.
Equivalent to `List.card (List.dedup l)` but more concise. -/
def distinctCount (l : List α) [DecidableEq α] : Nat := l.toFinset.card

lemma distinctCount_nil {α : Type u} [DecidableEq α] : distinctCount ([] : List α) = 0 := by
  simp [distinctCount]

lemma distinctCount_nonneg {α : Type u} [DecidableEq α] (l : List α) : 0 ≤ distinctCount l := by
  simp [distinctCount]

lemma distinctCount_nil_le {α : Type u} [DecidableEq α] (k : Nat) : distinctCount ([] : List α) ≤ k := by
  simp [distinctCount]

lemma distinctCount_singleton {α : Type u} [DecidableEq α] (a : α) : distinctCount [a] = 1 := by
  simp [distinctCount]

/-! ### Nodup list length vs Finset cardinality -/

/-- If a Nodup list's elements are all in a Finset, its length is bounded by the Finset's card.
This is useful for proving upper bounds on result lengths in combinatorial optimization:
if you construct a Nodup list of feasible values and every feasible value belongs to a known
Finset (e.g., all days in a range), then the list length ≤ the Finset's cardinality. -/
theorem length_le_card_of_subset {α : Type} [DecidableEq α] {D' : List α} {S : Finset α}
    (hnodup : D'.Nodup) (hsub : ∀ x ∈ D', x ∈ S) : D'.length ≤ S.card := by
  have h_card_toFinset : D'.toFinset.card = D'.length := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hnodup]
  have h_sub_finset : D'.toFinset ⊆ S := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact hsub x hx
  have h_card_le : D'.toFinset.card ≤ S.card := Finset.card_le_card h_sub_finset
  rw [h_card_toFinset] at h_card_le
  exact h_card_le


/-! ### Count distinct elements -/

/-- Number of distinct elements in a list.
`uniqCount l = |{x | x ∈ l}|`, counting each element at most once. -/
def uniqCount {α : Type} [DecidableEq α] (l : List α) : Nat :=
  (l.eraseDup).length

/-- Count the number of distinct elements in a list that satisfy a predicate `p`.
`countDistinctPred p l = |{x ∈ l | p x}|`, counting each element at most once.
Equivalent to `uniqCount (l.filter p)`. -/
def countDistinctPred {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) : Nat :=
  (l.filter p |>.eraseDup).length

lemma countDistinctPred_nil {α : Type} [DecidableEq α] (p : α → Bool) :
    countDistinctPred p ([] : List α) = 0 :=
  rfl

lemma countDistinctPred_eq_uniqCount_filter {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) :
    countDistinctPred p l = uniqCount (l.filter p) := by
  simp [countDistinctPred, uniqCount]


/-! ### `count` — convenience lemmas extending `List.count` -/

/-- If `count a l ≠ 0`, then `a ∈ l`.
This is the `≠ 0` counterpart of `count_pos_iff_mem`. -/
lemma mem_of_count_ne_zero {α : Type u} [BEq α] [LawfulBEq α] {a : α} {l : List α}
    (h : count a l ≠ 0) : a ∈ l :=
  count_pos_iff.mp (Nat.pos_of_ne_zero h)

/-- `List.count a l = 0` iff `a` is not in `l`.
This combines `count_eq_zero_of_not_mem` (←) with the forward direction
derived from `count_pos_iff`. Useful when both directions are needed simultaneously. -/
lemma count_eq_zero_iff_not_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} :
    List.count a l = 0 ↔ a ∉ l := by
  constructor
  · intro h hmem
    have hpos : 0 < List.count a l := (List.count_pos_iff.mpr hmem)
    omega
  · exact List.count_eq_zero_of_not_mem

/-- If every element in `l` whose `count` equals `k` equals `a`, then any element
in `l.filter (λ x => count x l = k)` equals `a`.
This generalizes the uniqueness reasoning pattern: all elements with a given
count value coincide, so the filter contains only `a`. -/
lemma mem_of_mem_filter_count_eq {α : Type u} [BEq α] [LawfulBEq α] {l : List α} {x a : α} {k : Nat}
    (h_unique : ∀ b ∈ l, count b l = k → b = a)
    (hx : x ∈ l.filter (λ x => count x l = k)) : x = a := by
  rcases List.mem_filter.mp hx with ⟨hxmem, hxcount⟩
  have hxcount_val : count x l = k := by simpa using hxcount
  exact h_unique x hxmem hxcount_val

/-- When `n > 0`, `l.any (fun x => l.count x == n) = true` iff there exists an element
whose count in `l` equals `n`. The `n > 0` condition is needed because `count x l = n > 0`
implies `x ∈ l`, bridging the existential from `List.any_eq_true` (which already carries
the membership condition) to the simpler `∃ x, l.count x = n`. -/
lemma any_count_pos_eq_true_iff {α : Type u} [BEq α] [LawfulBEq α] (l : List α) {n : Nat} (hn : n > 0) :
    l.any (fun x => l.count x == n) = true ↔ ∃ x, l.count x = n := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨x, _, hx⟩ := h
    refine ⟨x, ?_⟩
    simpa using hx
  · intro h
    obtain ⟨x, hx⟩ := h
    have hpos : 0 < l.count x := by
      rw [hx]
      exact hn
    have hmem : x ∈ l := (List.count_pos_iff.mp hpos)
    rw [List.any_eq_true]
    refine ⟨x, hmem, ?_⟩
    simp [hx]

/-- When `n > 0`, `l.any (fun x => l.count x == n) = false` iff every element's count
in `l` differs from `n`. This is the negation counterpart of `any_count_pos_eq_true_iff`. -/
lemma any_count_pos_eq_false_iff {α : Type u} [BEq α] [LawfulBEq α] (l : List α) {n : Nat} (hn : n > 0) :
    l.any (fun x => l.count x == n) = false ↔ ∀ x, l.count x ≠ n := by
  constructor
  · intro hFalse x hx
    have hTrue : l.any (fun x => l.count x == n) = true :=
      (any_count_pos_eq_true_iff l hn).mpr ⟨x, hx⟩
    rw [hFalse] at hTrue
    exact Bool.false_ne_true hTrue
  · intro hAll
    by_cases h : l.any (fun x => l.count x == n)
    · have hTrue : l.any (fun x => l.count x == n) = true := by
        cases h' : l.any (fun x => l.count x == n)
        · exact h'.symm ▸ h
        · rfl
      have ⟨x, hx⟩ := (any_count_pos_eq_true_iff l hn).mp hTrue
      exact absurd hx (hAll x)
    · simpa using h

/-- If all elements of `xs` are ≤ `M` and `M < a`, then `a ∉ xs`, so `count a xs = 0`.
This is a convenience lemma combining a universal upper bound with `count_eq_zero_of_not_mem`. -/
lemma count_eq_zero_of_all_le (xs : List Nat) (M a : Nat) (h_bound : ∀ x ∈ xs, x ≤ M) (h_lt : M < a) :
    count a xs = 0 := by
  apply count_eq_zero_of_not_mem
  intro hm
  have ha_le_M := h_bound a hm
  omega


/-! ### Unique elements — elements that appear exactly once -/

/-- Filter a list to retain only elements that appear exactly once.
`uniqueElems xs` returns the sublist of `xs` consisting of elements whose
`List.count` in `xs` is exactly `1`. Elements appearing 0 or ≥2 times are
dropped. -/
def uniqueElems {α : Type} [BEq α] (xs : List α) : List α :=
  xs.filter (fun x => xs.count x = 1)


end List

namespace List

/-! ### `toFinset` subset pigeonhole principle -/

/-- If a subset `S` of `l.toFinset` has cardinality equal to `l.length`, then `S` must equal
`l.toFinset`. This is a pigeonhole-principle argument. -/
lemma toFinset_eq_of_subset_card {α : Type} [DecidableEq α] {l : List α} {S : Finset α}
    (h_sub : S ⊆ l.toFinset) (h_card_eq : S.card = l.length) : S = l.toFinset := by
  have hle : l.toFinset.card ≤ l.length := List.toFinset_card_le (l := l)
  have hge : l.length ≤ l.toFinset.card :=
    calc
      l.length = S.card := by rw [h_card_eq]
      _ ≤ l.toFinset.card := Finset.card_le_card h_sub
  have h_card_toFinset : l.toFinset.card = l.length := le_antisymm hle hge
  exact Finset.eq_of_subset_of_card_le h_sub (by
    rw [h_card_toFinset, h_card_eq])

end List


namespace List

/-! ### List difference — elements of `xs` not in `ys` -/

/-- Elements of `xs` that are not in `ys`, with duplicates removed.
This is the list-level analogue of Finset subtraction (`s \\ t`) but operating on
arbitrary lists, removing duplicates from `xs` before filtering by non-membership in `ys`. -/
def listDiff [DecidableEq α] (xs ys : List α) : List α :=
  (xs.dedup).filter (λ x => decide (x ∉ ys))

/-- `listDiff xs ys` has no duplicate elements.
This follows from `List.Nodup.dedup` (which guarantees `dedup xs` has `Nodup`)
and the fact that `filter` preserves `Nodup`. -/
lemma nodup_listDiff [DecidableEq α] (xs ys : List α) : List.Nodup (listDiff xs ys) :=
  List.Nodup.filter _ (List.nodup_dedup xs)

end List

namespace List

/-! ### List intersection — nodup preservation -/

/-- If `l₁` has no duplicates, then `l₁.inter l₂` also has no duplicates.
`List.inter` is defined as `filter (elem · l₂) l₁`, so this follows from `List.Nodup.filter`. -/
lemma nodup_inter {α : Type u} [DecidableEq α] (l₁ l₂ : List α) (h : List.Nodup l₁) :
    List.Nodup (l₁.inter l₂) := by
  -- `List.inter` is defined via `BEq`, but when `DecidableEq` is available, it's equivalent
  -- to `filter (fun x => l₂.contains x) l₁`
  simpa [List.inter] using List.Nodup.filter (fun s => l₂.contains s) h

/-! ### `intersect_dedup` — deduplicated list intersection -/

/-- Intersect two lists and remove duplicates, returning a `Nodup` list
of elements that appear in both inputs. -/
def intersect_dedup {α : Type} [DecidableEq α] (l1 l2 : List α) : List α :=
  (l1.inter l2).dedup

/-- `intersect_dedup l1 l2` has no duplicate elements. -/
lemma nodup_intersect_dedup {α : Type} [DecidableEq α] (l1 l2 : List α) :
    List.Nodup (intersect_dedup l1 l2) := by
  dsimp [intersect_dedup]
  exact List.nodup_dedup _

/-- `a` is in `intersect_dedup l1 l2` iff `a` is in both `l1` and `l2`. -/
lemma mem_intersect_dedup_iff {α : Type} [DecidableEq α] {a : α} (l1 l2 : List α) :
    a ∈ intersect_dedup l1 l2 ↔ a ∈ l1 ∧ a ∈ l2 := by
  dsimp [intersect_dedup]
  constructor
  · intro h
    have hmem := (List.mem_dedup (a := a)).mp h
    exact And.intro (List.mem_of_mem_inter_left hmem) (List.mem_of_mem_inter_right hmem)
  · intro ⟨h₁, h₂⟩
    apply (List.mem_dedup (a := a)).mpr
    exact List.mem_inter_of_mem_of_mem h₁ h₂

end List

namespace List

/-! ### List subset (membership-based) -/

/-- `isSubset a b` means every element of `a` is also an element of `b`.
This is the list-as-set subset notion, ignoring multiplicities and order.
Compare with `List.Sublist` which requires order-preservation. -/
def isSubset {α : Type} (a b : List α) : Prop :=
  ∀ s, s ∈ a → s ∈ b

/-- The empty list is a subset of any list. -/
lemma nil_isSubset {α : Type} (l : List α) : isSubset [] l := by
  intro e he
  simp at he

end List

namespace List

/-! ### Enum membership lemmas -/

/-- If `i` is a valid index into `xs`, then `(i, xs[i])` appears in `xs.enum`. -/
lemma getElem_mem_enum {α : Type} {xs : List α} {i : Nat} (h : i < xs.length) :
    (i, xs[i]) ∈ xs.enum := by
  have hlen : i < xs.enum.length := by
    rw [List.enum_length]
    exact h
  rw [List.mem_iff_getElem]
  refine ⟨i, hlen, ?_⟩
  rw [List.getElem_enum]

end List

namespace List

/-! ### `all_len_ge` — minimum length constraint on sublists -/

/-- Predicate: every inner list in `l` has length at least `n`.
Reusable across any problem that needs a minimum-length constraint on sublists. -/
def all_len_ge {α : Type u} (n : Nat) (l : List (List α)) : Prop :=
  Forall (fun a => a.length ≥ n) l


lemma all_len_ge_nil {α : Type u} {n : Nat} : all_len_ge n ([] : List (List α)) := by
  unfold all_len_ge
  simp

/-! ### `all_lt` — every element is strictly less than a bound -/

/-- Predicate: every element in `xs` is strictly less than `bound`.
Reusable precondition for bound-checking on list values, e.g. ensuring all bytes are < 256. -/
def all_lt {α : Type} [LT α] (bound : α) (xs : List α) : Prop :=
  ∀ b ∈ xs, b < bound


lemma all_lt_nil {α : Type} [LT α] {bound : α} : all_lt bound ([] : List α) := by
  unfold all_lt; simp

lemma all_lt_cons {α : Type} [LT α] {bound a : α} {as : List α} :
    all_lt bound (a :: as) ↔ a < bound ∧ all_lt bound as := by
  unfold all_lt; simp

/-! ### `eraseDup` properties -/

/-- `l.eraseDup` has no duplicate elements.
This is a fundamental lemma used across many LeetCode/open-source problems. -/
lemma nodup_eraseDup {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    (l.eraseDup).Nodup := by
  have h_irrefl : ∀ (x : α), (x != x) ≠ true := by
    intro x; simp
  rw [List.eraseDup]
  induction' l with h t ih
  · exact List.nodup_nil
  · rw [List.pwFilter, List.foldr]
    split
    · rename_i hcond
      refine List.Nodup.cons ?_ ih
      intro hmem
      have hy := hcond h hmem
      exact h_irrefl h hy
    · exact ih

/-- `List.eraseDup` never increases the length of a list.
Together with `nodup_eraseDup`, this gives the key properties of `eraseDup`:
it removes duplicates (`nodup_eraseDup`) while never growing the list
(`eraseDup_length_le`). -/
lemma eraseDup_length_le {α : Type} [DecidableEq α] (l : List α) :
    (l.eraseDup).length ≤ l.length := by
  induction l with
  | nil => simp [List.eraseDup]
  | cons x xs ih =>
      have h_eq : (x :: xs).eraseDup =
          (if ∀ y ∈ xs.eraseDup, x ≠ y then x :: xs.eraseDup else xs.eraseDup) := by
        unfold List.eraseDup List.pwFilter; simp
      rw [h_eq]
      split
      · simp; omega
      · simp; omega

/-- If a nodup list has all elements equal to `m`, then its length is at most 1. -/
lemma length_le_one_of_nodup_all_eq {α : Type} {l : List α} {m : α}
    (hnodup : l.Nodup) (hall : ∀ x ∈ l, x = m) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    have hx : x = m := hall x (by simp)
    have hy : y = m := hall y (by simp)
    subst hx; subst hy
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hnotmem, _⟩
    simp at hnotmem

end List


namespace List

/-! ### `dedup` preserves `Sorted` -/

/-- If a list is `Sorted` by relation `r`, then `dedup` preserves the sortedness:
`l.dedup` is also sorted by `r`. This is a general lemma about `List.dedup` — it
removes all duplicates (not just consecutive ones) while respecting the original sort order. -/
lemma sorted_dedup_of_sorted {α : Type} [DecidableEq α] {r : α → α → Prop} {l : List α}
    (h : List.Sorted r l) : List.Sorted r (l.dedup) := by
  induction l with
  | nil => exact List.sorted_nil
  | cons a l ih =>
    have h_tail : List.Sorted r l := h.of_cons
    have ih_sorted : List.Sorted r (l.dedup) := ih h_tail
    by_cases ha : a ∈ l.dedup
    · rw [List.dedup_cons_of_mem' ha]
      exact ih_sorted
    · rw [List.dedup_cons_of_not_mem' ha]
      apply (List.sorted_cons (r := r) (a := a) (l := l.dedup)).mpr
      constructor
      · intro x hx
        have hx_in_l : x ∈ l := (List.mem_dedup (l := l)).mp hx
        have hall : ∀ b ∈ l, r a b := ((List.sorted_cons (a := a) (l := l)).mp h).left
        exact hall x hx_in_l
      · exact ih_sorted

/-! ### `sortDedup` — sort and deduplicate with `insertionSort` -/

/-- Sort a list with `insertionSort` and then remove duplicates via `dedup`.
The result is sorted by `r`, has no duplicates, and contains exactly the same elements
as the input. Parameterized by any decidable relation `r`.
For the `LinearOrder` special case, use `sortDedup (· ≤ ·) l`. -/
def sortDedup {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) : List α :=
  (List.insertionSort r l).dedup

/-- `sortDedup r l` has no duplicate elements. -/
lemma sortDedup_nodup {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) :
    List.Nodup (sortDedup r l) :=
  List.nodup_dedup (l.insertionSort r)

/-- `sortDedup r l` is `Pairwise` sorted by `r`.
Requires `IsTotal` and `IsTrans` for `insertionSort` sortedness. -/
lemma sortDedup_sorted {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l : List α) :
    List.Pairwise r (sortDedup r l) :=
  sorted_dedup_of_sorted (List.sorted_insertionSort r l)

/-- Membership in `sortDedup r l` is equivalent to membership in `l`. -/
lemma mem_sortDedup {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (l : List α) (x : α) :
    x ∈ sortDedup r l ↔ x ∈ l := by
  simp [sortDedup, List.mem_dedup, List.mem_insertionSort]

/-- `sortDedup r l` is nodup, sorted by `r`, and has the same membership as `l`.
This bundles the three key properties into a single lemma for convenience. -/
lemma sortDedup_properties {α : Type} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
    (sortDedup r l).Nodup ∧
    List.Sorted r (sortDedup r l) ∧
    (∀ x, x ∈ sortDedup r l ↔ x ∈ l) :=
  ⟨sortDedup_nodup r l, sortDedup_sorted r l, mem_sortDedup r l⟩

/-- `sortDedup` specialized to `(· ≤ ·)` on a `LinearOrder` (convenience alias). -/
def sortDedup_le {α : Type} [LinearOrder α] (l : List α) : List α :=
  sortDedup (· ≤ ·) l

/-- General version of `sortDedup_properties`: for any relation `r` that is total and transitive,
`(insertionSort r l).dedup` is sorted by `r`, nodup, and has the same elements as `l`.
This lemma works with any decidable relation, not just `≤` from a `LinearOrder`. -/
theorem insertionSort_dedup_properties {α : Type} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
    List.Sorted r ((List.insertionSort r l).dedup) ∧
    List.Nodup ((List.insertionSort r l).dedup) ∧
    (∀ x : α, x ∈ (List.insertionSort r l).dedup ↔ x ∈ l) := by
  rcases sortDedup_properties r l with ⟨hn, hs, hm⟩
  unfold sortDedup at hn hs hm
  exact ⟨hs, hn, hm⟩

/-! ### `dedup.mergeSort` properties -/

/-- `List.mergeSort` preserves length, is a permutation of the input (as `List.Perm`),
    and produces a list sorted by `r` under the `List.Pairwise` condition
    (given transitivity and totality of `r`). -/
lemma mergeSort_sorted_perm_length {α : Type} (l : List α) (r : α → α → Bool)
    (h_trans : ∀ a b c, r a b = true → r b c = true → r a c = true)
    (h_total : ∀ a b, (r a b || r b a) = true) :
    (List.mergeSort l r).length = l.length ∧
    List.mergeSort l r ~ l ∧
    List.Pairwise (fun a b => r a b = true) (List.mergeSort l r) := by
  have h_perm : List.mergeSort l r ~ l := List.mergeSort_perm l r
  have h_sorted : List.Pairwise (fun a b => r a b = true) (List.mergeSort l r) :=
    List.sorted_mergeSort h_trans h_total l
  exact ⟨List.length_mergeSort l, h_perm, h_sorted⟩

/-- `l.dedup.mergeSort (· ≤ ·)` is sorted. -/
lemma sorted_dedup_mergeSort {α : Type} [LinearOrder α] (l : List α) :
    List.Sorted (· ≤ ·) (l.dedup.mergeSort (· ≤ ·)) :=
  List.sorted_mergeSort' (· ≤ ·) (l.dedup)

/-- `l.dedup.mergeSort r` contains no duplicates. -/
lemma nodup_dedup_mergeSort {α : Type} [DecidableEq α] (r : α → α → Bool) (l : List α) :
    List.Nodup (l.dedup.mergeSort r) := by
  rw [List.nodup_mergeSort]
  exact List.nodup_dedup l

/-- If `a` is in `l`, then `a` is also in `l.dedup.mergeSort r`. -/
lemma mem_dedup_mergeSort {α : Type} [DecidableEq α] (r : α → α → Bool) (l : List α) (a : α) (ha : a ∈ l) :
    a ∈ l.dedup.mergeSort r := by
  have hmem_dedup : a ∈ l.dedup := (List.mem_dedup).mpr ha
  exact ((List.mergeSort_perm l.dedup r).mem_iff).mpr hmem_dedup

/-- A list merge-sorted with the `(a ≤ b)` comparator is pairwise ordered
by `decide (a ≤ b) = true`. Works for any `LinearOrder` type.
This specializes `List.sorted_mergeSort` with `decide_le_trans` and `decide_le_total`. -/
lemma mergeSort_sorted_le {α : Type} [LinearOrder α] (l : List α) :
    List.Pairwise (fun a b => decide (a ≤ b) = true) (l.mergeSort (fun a b => a ≤ b)) := by
  simpa using (List.sorted_mergeSort' (· ≤ ·) l)

/-- If a list is pairwise related by `decide (R a b) = true`, then it is also
pairwise related by the propositional relation `R` itself.
This bridges the boolean `decide`-wrapped version of `List.Pairwise` to the `Prop` version,
which is useful when `List.sorted_mergeSort` provides pairwise `decide` and the rest of the
proof works with the `Prop` relation (e.g., `(· ≤ ·)` rather than `fun a b => decide (a ≤ b) = true`). -/
lemma pairwise_decide_eq_true {α : Type} {R : α → α → Prop} [DecidableRel R] {l : List α}
    (h : List.Pairwise (fun a b => decide (R a b) = true) l) : List.Pairwise R l := by
  apply h.imp
  intro a b h_eq
  simpa using decide_eq_true_iff.mp h_eq

/-- If `l` is nodup, then to lift a `Pairwise R` to `Pairwise S`, it suffices
to know that `R a b → S a b` for *distinct* `a` and `b`.
This is a strengthening of `Pairwise.imp` that only requires the implication
to hold when the elements are different (which is always the case for pairwise
comparisons in a nodup list). -/
lemma Pairwise.imp_of_nodup {α : Type} {R S : α → α → Prop} {l : List α}
    (hp : List.Pairwise R l) (h_nd : l.Nodup) (H : ∀ a b, a ≠ b → R a b → S a b) :
    List.Pairwise S l := by
  revert h_nd
  induction hp with
  | nil =>
    intro h_nd; exact Pairwise.nil
  | cons h₁ h₂ ih =>
    intro h_nd
    rename_i a tail
    cases h_nd with
    | cons h_notmem h_nd_tail =>
      apply Pairwise.cons
      · intro a' ha'
        have h_ne : a ≠ a' := h_notmem a' ha'
        apply H a a' h_ne (h₁ a' ha')
      · exact ih h_nd_tail

/-- If a list is `Pairwise` ordered by `decide (a ≤ b) = true` and has no duplicates,
then it is `Pairwise` ordered by the strict relation `(· < ·)`.
This bridges non-strict sortedness + nodup to strict sortedness. -/
lemma pairwise_lt_of_pairwise_decide_le_nodup {α : Type} [LinearOrder α] (l : List α)
    (h_pairwise : List.Pairwise (fun a b => decide (a ≤ b) = true) l) (h_nodup : l.Nodup) :
    List.Pairwise (· < ·) l := by
  rw [List.pairwise_iff_get] at h_pairwise ⊢
  intro i j hij
  have hle := h_pairwise i j hij
  have hle' : l.get i ≤ l.get j := by
    simpa using hle
  have hne : l.get i ≠ l.get j := by
    have h_inj := h_nodup.get_inj_iff (i := i) (j := j)
    intro heq
    have heq_idx : i = j := h_inj.mp heq
    have : ¬ (i < j) := by
      subst heq_idx
      exact Fin.lt_irrefl _
    exact this hij
  exact lt_of_le_of_ne hle' hne

/-- A Nodup list merge-sorted with `(≤)` is strictly increasing
(pairwise `<`). Combines sortedness and nodup into the `<` relation.
Works for any `LinearOrder` type. -/
lemma nodup_mergeSort_pairwise_lt {α : Type} [LinearOrder α] (l : List α) (h_nodup : l.Nodup) :
    List.Pairwise (· < ·) (l.mergeSort (fun a b => a ≤ b)) := by
  have h_sorted_decide : List.Pairwise (fun a b => decide (a ≤ b) = true) (l.mergeSort (fun a b => a ≤ b)) :=
    mergeSort_sorted_le l
  have h_sorted_nodup : (l.mergeSort (fun a b => a ≤ b)).Nodup :=
    (List.nodup_mergeSort (le := fun a b => a ≤ b)).mpr h_nodup
  exact pairwise_lt_of_pairwise_decide_le_nodup (l.mergeSort (fun a b => a ≤ b)) h_sorted_decide h_sorted_nodup

/-! ### k-th smallest element via sorting -/

/-- Returns the `k`-th smallest element of `vals` (sorted non-decreasing by `≤`),
    or `none` if `vals` has fewer than `k` elements.

    The 1st smallest is the minimum, the 2nd smallest is the second minimum, etc.
    When `k = 0`, `k-1` underflows to `0` in `Nat`, returning the first element
    of the sorted list (which is the minimum). -/
def kthSmallest {α : Type} [LinearOrder α] (k : Nat) (vals : List α) : Option α :=
  if h : vals.length < k then
    none
  else
    (vals.mergeSort (· ≤ ·))[k-1]?

/-- `List.elem` is preserved by `insertionSort`: an element is in the sorted list
iff it is in the original list (by boolean membership). -/
lemma elem_insertionSort_eq {α : Type} [BEq α] [LawfulBEq α] (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    List.elem x (List.insertionSort r xs) = List.elem x xs := by
  simp [List.elem_eq_mem, List.mem_insertionSort]

/-- `insertionSort` is permutation-invariant: sorting two permutation-related lists
with the same total, transitive, and antisymmetric relation yields identical results.
For `LinearOrder α`, this works with both `(· ≤ ·)` and `(· ≥ ·)`. -/
lemma insertionSort_eq_of_perm {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] [IsAntisymm α r]
    (l₁ l₂ : List α) (h_perm : List.Perm l₁ l₂) :
    List.insertionSort r l₁ = List.insertionSort r l₂ :=
  List.eq_of_perm_of_sorted
    (List.Perm.trans (List.perm_insertionSort r l₁)
      (List.Perm.trans h_perm ((List.perm_insertionSort r l₂).symm)))
    (List.sorted_insertionSort r l₁)
    (List.sorted_insertionSort r l₂)

end List


namespace List

/-! ### `dedupSorted` — remove consecutive duplicates from a sorted list -/

/-- Remove consecutive duplicates from a list. This is efficient (O(n))
when the input is already sorted, since only adjacent equal elements are removed.
Contrast with `List.eraseDup` / `List.dedup` which remove all duplicates regardless of position
but have worse time complexity.

`dedupSorted` on a sorted list yields the same result as `List.eraseDup`,
but with linear time complexity. -/
def dedupSorted {α} [DecidableEq α] : List α → List α
  | []            => []
  | [x]           => [x]
  | x :: y :: zs  => if x = y then dedupSorted (y :: zs) else x :: dedupSorted (y :: zs)

/-- If `x` is in `dedupSorted l`, then `x` is also in `l`. -/
lemma mem_dedupSorted {α} [DecidableEq α] {x : α} {l : List α} (h : x ∈ dedupSorted l) : x ∈ l := by
  induction l with
  | nil => simp [dedupSorted] at h
  | cons hd tl ih =>
    cases tl with
    | nil => simpa [dedupSorted] using h
    | cons hd' tl' =>
      simp only [dedupSorted] at h ⊢
      split at h
      · have hmem := ih h
        simp only [List.mem_cons] at hmem ⊢
        rcases hmem with (rfl | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hm)
      · simp only [List.mem_cons] at h ⊢
        rcases h with (rfl | hm)
        · exact Or.inl rfl
        · have hmem := ih hm
          simp only [List.mem_cons] at hmem ⊢
          rcases hmem with (rfl | hm')
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hm')

/-- If `l` is sorted by `(· ≤ ·)`, then `dedupSorted l` is also sorted by `(· ≤ ·)`. -/
lemma sorted_dedupSorted {α} [LE α] [DecidableEq α] {l : List α} (h : List.Sorted (· ≤ ·) l) :
    List.Sorted (· ≤ ·) (dedupSorted l) := by
  induction l with
  | nil => simp [dedupSorted]
  | cons hd tl ih =>
    cases tl with
    | nil => simp [dedupSorted]
    | cons hd' tl' =>
      rw [List.sorted_cons] at h
      rcases h with ⟨h_all, h_tl_sorted⟩
      simp only [dedupSorted]
      split
      · apply ih h_tl_sorted
      · have h_dedup_tl_sorted := ih h_tl_sorted
        rw [List.sorted_cons]
        constructor
        · intro x hx
          have hx_in : x ∈ hd' :: tl' := mem_dedupSorted hx
          exact h_all x hx_in
        · exact h_dedup_tl_sorted

/-- Membership in `dedupSorted l` is equivalent to membership in `l`. -/
lemma mem_dedupSorted_iff {α : Type u} [DecidableEq α] (x : α) (l : List α) :
    x ∈ dedupSorted l ↔ x ∈ l := by
  induction' l with y ys ih
  · simp [dedupSorted]
  · cases ys with
    | nil => simp [dedupSorted]
    | cons z zs =>
      simp [dedupSorted]
      by_cases hyz : y = z
      · subst hyz; simp [ih]
      · simp [hyz, ih]

/-- `dedupSorted` produces a nodup list when the input is sorted (by `(· ≤ ·)`). -/
lemma dedupSorted_nodup {α : Type u} [LinearOrder α] (l : List α)
    (hsorted : List.Sorted (· ≤ ·) l) : (dedupSorted l).Nodup := by
  induction' l with x l ih
  · simp [dedupSorted]
  · cases l with
    | nil => simp [dedupSorted]
    | cons y ys =>
      rw [List.sorted_cons] at hsorted
      rcases hsorted with ⟨hx_le_all, h_sorted_yys⟩
      rw [List.sorted_cons] at h_sorted_yys
      rcases h_sorted_yys with ⟨hy_le_all, h_sorted_ys⟩
      simp [dedupSorted]
      by_cases h_eq : x = y
      · simp [h_eq]
        have h_sorted_yys' : List.Sorted (· ≤ ·) (y :: ys) := by
          rw [List.sorted_cons]; exact ⟨hy_le_all, h_sorted_ys⟩
        exact ih h_sorted_yys'
      · rw [if_neg h_eq]
        have ih_rest : (dedupSorted (y :: ys)).Nodup := by
          have h_sorted_yys' : List.Sorted (· ≤ ·) (y :: ys) := by
            rw [List.sorted_cons]; exact ⟨hy_le_all, h_sorted_ys⟩
          exact ih h_sorted_yys'
        apply List.Nodup.cons
        · intro hx_in
          have hx_in_orig : x ∈ y :: ys := by
            rw [← mem_dedupSorted_iff]; exact hx_in
          have hx_simp : x = y ∨ x ∈ ys := List.mem_cons.mp hx_in_orig
          rcases hx_simp with (hxy | hx_in_ys)
          · exact h_eq hxy
          · have hy_lex : y ≤ x := hy_le_all x hx_in_ys
            have hx_ley : x ≤ y := hx_le_all y (by simp)
            exact h_eq (le_antisymm hx_ley hy_lex)
        · exact ih_rest

/-! ### `dedupConsecutive` — remove consecutive duplicates using `BEq` -/

/-- Remove consecutive duplicate elements from a list.
This is a variant of `dedupSorted` that works with `BEq α` instead of `DecidableEq α`,
making it suitable for use in generic code that only has `BEq` available.

For example: `dedupConsecutive [1,1,2,2,2,3,1] = [1,2,3,1]`. -/
def dedupConsecutive {α : Type} [BEq α] : List α → List α
  | [] => []
  | [c] => [c]
  | c1 :: c2 :: rest =>
    if c1 == c2 then dedupConsecutive (c1 :: rest)
    else c1 :: dedupConsecutive (c2 :: rest)

/-! ### `dedupRight` — remove duplicates, keeping the last occurrence

This is the right-to-left variant of `List.dedup`. Whereas `List.dedup` keeps the
first occurrence of each element, `dedupRight` keeps the *last* occurrence.
Equivalently, `dedupRight l = (l.reverse.dedup).reverse`.

For example: `dedupRight [1,2,3,2,1] = [3,2,1]` (compared to
`List.dedup [1,2,3,2,1] = [1,2,3]`). -/

/-- Remove duplicate elements from a list, keeping the rightmost (last) occurrence
of each value. The result has the same set of elements as the original list
but with no duplicates. Equivalent to `(l.reverse.dedup).reverse`.
For example: `dedupRight [1,2,3,2,1] = [3,2,1]`. -/
def dedupRight {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
    if x ∈ xs then dedupRight xs
    else x :: dedupRight xs

/-- Membership in `dedupRight l` is equivalent to membership in `l`. -/
theorem mem_dedupRight {α : Type} [DecidableEq α] (a : α) (l : List α) :
    a ∈ dedupRight l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedupRight]
  | cons x xs ih =>
    simp [dedupRight]
    split
    · rename_i hx_in_xs
      constructor
      · intro ha_dedup
        have ha_in_xs : a ∈ xs := ih.mp ha_dedup
        exact Or.inr ha_in_xs
      · intro ha_cons
        rcases ha_cons with (rfl | ha_in_xs)
        · apply ih.mpr; exact hx_in_xs
        · apply ih.mpr; exact ha_in_xs
    · rename_i hx_notin_xs
      simp [ih, List.mem_cons]

/-- `dedupRight l` has no duplicate elements. -/
theorem nodup_dedupRight {α : Type} [DecidableEq α] (l : List α) :
    (dedupRight l).Nodup := by
  induction l with
  | nil => simp [dedupRight]
  | cons x xs ih =>
    simp [dedupRight]
    split
    · exact ih
    · rename_i h_notin
      apply List.Nodup.cons
      · intro h
        have hx : x ∈ xs := (mem_dedupRight x xs).mp h
        exact h_notin hx
      · exact ih

end List


namespace List

/-! ### `dedupMap` — map then deduplicate -/

/-- Map a function `f : α → β` over `xs : List α`, then deduplicate the result by `β`. -/
def dedupMap {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) : List β :=
  (List.map f xs).dedup

/-- `dedupMap f xs` has no duplicates, and membership in it is equivalent to existence
of a preimage under `f` in `xs`. -/
theorem dedupMap_nodup_and_mem {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    List.Nodup (dedupMap f xs) ∧ ∀ y, y ∈ dedupMap f xs ↔ ∃ x ∈ xs, f x = y := by
  unfold dedupMap
  constructor
  · apply List.nodup_dedup
  · intro y
    simp [List.mem_dedup, List.mem_map]

/-- `dedupMap f xs` is nodup. Convenience lemma extracting the nodup conjunct
from `dedupMap_nodup_and_mem`. -/
lemma nodup_dedupMap {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    (dedupMap f xs).Nodup :=
  (dedupMap_nodup_and_mem f xs).left

/-- If `x ∈ xs`, then `f x ∈ dedupMap f xs`. Membership is preserved through map-dedup. -/
lemma mem_dedupMap_of_mem {α β : Type} [DecidableEq β] (f : α → β) {x : α} {xs : List α}
    (h : x ∈ xs) : f x ∈ dedupMap f xs :=
  ((dedupMap_nodup_and_mem f xs).right (f x)).mpr ⟨x, h, rfl⟩

/-- If `y ∈ dedupMap f xs`, then there exists `x ∈ xs` such that `f x = y`.
Convenience lemma extracting the forward direction of the membership equivalence. -/
lemma mem_of_mem_dedupMap {α β : Type} [DecidableEq β] (f : α → β) {y : β} {xs : List α}
    (h : y ∈ dedupMap f xs) : ∃ x ∈ xs, f x = y :=
  ((dedupMap_nodup_and_mem f xs).right y).mp h

/-! ### `dedupInsert` — insert without duplication -/

/-- Insert `f x` into `acc` if it is not already present, deduplicating entries by key.
`foldr (dedupInsert f) [] xs` produces the deduplicated list of `f` applied to each element of `xs`,
keeping the last occurrence of each value. Compare with `dedupMap` which keeps the first occurrence. -/
def dedupInsert {α β : Type} [DecidableEq β] (f : α → β) (x : α) (acc : List β) : List β :=
  if (f x) ∈ acc then acc else (f x) :: acc

/-- `dedupInsert f x` preserves `Nodup`: if `acc` has no duplicates, the result also has no duplicates. -/
lemma dedupInsert_nodup {α β : Type} [DecidableEq β] (f : α → β) (x : α) (acc : List β)
    (h : List.Nodup acc) : List.Nodup (dedupInsert f x acc) := by
  unfold dedupInsert
  split
  · exact h
  · rename_i hmem
    exact List.Nodup.cons hmem h

/-- Membership in `dedupInsert f x acc` is equivalent to `r = f x` or `r ∈ acc`. -/
lemma mem_dedupInsert_iff {α β : Type} [DecidableEq β] (f : α → β) (r : β) (x : α) (acc : List β) :
    r ∈ dedupInsert f x acc ↔ r = f x ∨ r ∈ acc := by
  unfold dedupInsert
  split
  · rename_i hmem
    constructor
    · intro hr; exact Or.inr hr
    · intro h
      rcases h with (hr | hr)
      · rw [hr]; exact hmem
      · exact hr
  · rename_i hmem
    simp

/-- Folding `dedupInsert f` over `xs` produces a nodup list. -/
lemma foldr_dedupInsert_nodup {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    List.Nodup (List.foldr (dedupInsert f) [] xs) := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    rw [List.foldr]
    exact dedupInsert_nodup f x (List.foldr (dedupInsert f) [] rest) ih

/-- Membership in `foldr (dedupInsert f) [] xs` is equivalent to the existence of
an `x ∈ xs` such that `f x = r`. This says that folding `dedupInsert` collects exactly
the image of `f` on `xs` (without duplicates). -/
lemma mem_foldr_dedupInsert_iff {α β : Type} [DecidableEq β] (f : α → β) (r : β) (xs : List α) :
    r ∈ List.foldr (dedupInsert f) [] xs ↔ ∃ x, x ∈ xs ∧ f x = r := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldr, mem_dedupInsert_iff f r x (List.foldr (dedupInsert f) [] rest), ih]
    refine ⟨?_, ?_⟩
    · intro h
      rcases h with (h_eq | ⟨w, hw_mem, hw_f⟩)
      · exact ⟨x, List.mem_cons_self x rest, h_eq.symm⟩
      · exact ⟨w, List.mem_cons_of_mem x hw_mem, hw_f⟩
    · intro h
      rcases h with ⟨w, hw_mem, hw_f⟩
      rw [List.mem_cons] at hw_mem
      rcases hw_mem with (hw_eq | hw_mem')
      · subst hw_eq; exact Or.inl hw_f.symm
      · exact Or.inr ⟨w, hw_mem', hw_f⟩

end List


namespace List

/-! ### `isPerm_refl` — reflexivity of `List.isPerm` -/

/-- `List.isPerm` is reflexive: every list is a permutation of itself. -/

lemma isPerm_refl [BEq α] [LawfulBEq α] (l : List α) : l.isPerm l = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.isPerm, ih]

/-! ### `hasPerm` — permutation membership check -/

/-- Check if any list in `acc` is a permutation of `d`. -/
def hasPerm {α : Type _} [DecidableEq α] (d : List α) (acc : List (List α)) : Bool :=
  acc.any (fun d' => decide (List.Perm d d'))

lemma hasPerm_iff {α : Type _} [DecidableEq α] (d : List α) (acc : List (List α)) :
    hasPerm d acc ↔ ∃ d' ∈ acc, List.Perm d d' := by
  simp [hasPerm, List.any_eq_true, decide_eq_true]

/-! ### `noPermDups` — no permutation-duplicate elements -/

/-- No two distinct elements in `l` are permutations of each other. -/
def noPermDups {α : Type _} (l : List (List α)) : Prop :=
  ∀ d₁ d₂, d₁ ∈ l → d₂ ∈ l → List.Perm d₁ d₂ → d₁ = d₂


lemma noPermDups_nil {α : Type _} : noPermDups ([] : List (List α)) := by
  intro d₁ d₂ h₁ h₂ _
  exfalso; exact List.not_mem_nil _ h₁

lemma noPermDups_cons_of_not_hasPerm {α : Type _} [DecidableEq α] (d : List α) (acc : List (List α))
    (hacc : noPermDups acc) (hnot : ¬ hasPerm d acc) : noPermDups (d :: acc) := by
  intro d₁ d₂ h₁ h₂ hperm
  simp at h₁ h₂
  rcases h₁ with (heq₁ | h₁)
  · -- d₁ = d
    rcases h₂ with (heq₂ | h₂)
    · -- d₂ = d
      rw [heq₁, heq₂]
    · -- d₂ ∈ acc
      have hperm' : List.Perm d d₂ := by rwa [heq₁] at hperm
      have h_not : ¬ ∃ d' ∈ acc, List.Perm d d' := by
        rwa [hasPerm_iff] at hnot
      exfalso; apply h_not; exact ⟨d₂, h₂, hperm'⟩
  · -- d₁ ∈ acc
    rcases h₂ with (heq₂ | h₂)
    · -- d₂ = d
      have hperm' : List.Perm d₁ d := by rwa [heq₂] at hperm
      have h_not : ¬ ∃ d' ∈ acc, List.Perm d d' := by
        rwa [hasPerm_iff] at hnot
      exfalso; apply h_not; exact ⟨d₁, h₁, List.Perm.symm hperm'⟩
    · -- d₂ ∈ acc
      exact hacc d₁ d₂ h₁ h₂ hperm

/-! ### `removePermDupsAux` — auxiliary permutation-deduplication -/

/-- Recursively remove permutation-duplicates by collecting unique entries.
The `remaining` list is scanned element by element; each element is kept only if
no permutation of it already exists in `acc` (first-seen-wins semantics). -/
def removePermDupsAux {α : Type _} [DecidableEq α] (remaining acc : List (List α)) : List (List α) :=
  match remaining with
  | [] => acc
  | d :: rest =>
    if hasPerm d acc then removePermDupsAux rest acc
    else removePermDupsAux rest (d :: acc)

/-! ### `uniquePermutationsList` — deduplicated permutations -/

/-- Returns the unique permutations of a list, with no duplicate entries.
Equivalent to `(List.permutations l).dedup`, i.e. all permutations of `l`
with duplicate-permutation entries removed. -/
def uniquePermutationsList {α : Type u} [DecidableEq α] (l : List α) : List (List α) :=
  (List.permutations l).dedup

/-- `uniquePermutationsList` produces a nodup result. -/
lemma nodup_uniquePermutationsList {α : Type u} [DecidableEq α] (l : List α) :
    List.Nodup (uniquePermutationsList l) :=
  List.nodup_dedup _

/-- Membership in `uniquePermutationsList` is equivalent to `List.Perm`:
`p` appears in the deduplicated permutations of `l` iff `p` is a permutation of `l`. -/
theorem mem_uniquePermutationsList_iff {α : Type u} [DecidableEq α] {l p : List α} :
    p ∈ uniquePermutationsList l ↔ List.Perm p l := by
  dsimp [uniquePermutationsList]
  constructor
  · intro h
    have hmem := List.mem_dedup.mp h
    exact ((List.mem_permutations (s := p) (t := l)).mp hmem)
  · intro h
    have hmem := (List.mem_permutations (s := p) (t := l)).mpr h
    exact List.mem_dedup.mpr hmem

end List


namespace List

/-! ### Uniqueness filtering -/

/-- Returns true iff `x` occurs exactly once in `l`. -/
def occursExactlyOnce {α : Type} [DecidableEq α] (l : List α) (x : α) : Bool :=
  decide ((l.filter (· = x)).length = 1)

/-- Filters a list to keep only elements that occur exactly once. -/
def filterUnique {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.filter (occursExactlyOnce l)

end List
