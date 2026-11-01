import Mathlib.Data.List.Basic
import Mathlib.Tactic
import fvapps.List.Sort
import fvapps.Nat

namespace Specific

open _root_.List

namespace List

/-! ## Sum over lists with `Nat` scores -/

/-- Sum a `Nat`-valued score function over a list. -/
def sumBy {β : Type} (f : β → Nat) : List β → Nat
  | [] => 0
  | x :: xs => f x + sumBy f xs

@[simp] theorem sumBy_nil {β : Type} (f : β → Nat) : sumBy f [] = 0 := rfl

@[simp] theorem sumBy_cons {β : Type} (f : β → Nat) (x : β) (xs : List β) :
    sumBy f (x :: xs) = f x + sumBy f xs := rfl

@[simp] theorem sumBy_singleton {β : Type} (f : β → Nat) (x : β) : sumBy f [x] = f x := by simp

/-! ## Max over lists with `Nat` scores -/

/-- Take the maximum of a `Nat`-valued score function over a list.
Returns `0` for the empty list. This is the max-analogue of `sumBy`. -/
def maxBy {β : Type} (f : β → Nat) : List β → Nat
  | [] => 0
  | x :: xs => max (f x) (maxBy f xs)

@[simp] theorem maxBy_nil {β : Type} (f : β → Nat) : maxBy f [] = 0 := rfl

@[simp] theorem maxBy_cons {β : Type} (f : β → Nat) (x : β) (xs : List β) :
    maxBy f (x :: xs) = max (f x) (maxBy f xs) := rfl

@[simp] theorem maxBy_singleton {β : Type} (f : β → Nat) (x : β) : maxBy f [x] = f x := by
  simp

/-- `foldl max` with a score function is equivalent to `max` of the
accumulator and `maxBy`. -/
lemma foldl_max_eq_max_maxBy {β : Type} (f : β → Nat) :
    ∀ xs : List β, ∀ acc : Nat,
      xs.foldl (fun acc x => max acc (f x)) acc = max acc (maxBy f xs)
  | [], acc => by simp
  | x :: xs, acc => by
      calc
        (x :: xs).foldl (fun acc x => max acc (f x)) acc
            = max (max acc (f x)) (maxBy f xs) := by
                simp [foldl_max_eq_max_maxBy f xs]
        _ = max acc (maxBy f (x :: xs)) := by
                simp [maxBy, max_assoc, max_left_comm, max_comm]

/-- `maxBy` equals the foldl form. -/
theorem maxBy_eq_foldl {β : Type} (f : β → Nat) (xs : List β) :
    maxBy f xs = xs.foldl (fun acc x => max acc (f x)) 0 := by
  rw [foldl_max_eq_max_maxBy]
  simp

/-! ## `sumMap`: map each element, then sum (generic `AddMonoid`)

`sumMap f [x₁, ..., xₙ] = f x₁ + ... + f xₙ`.  This generalizes `sumBy`
(which is specialized to `Nat`) to any `AddMonoid`-valued function. -/

/-- Sum `f x` over all `x` in the list, for any `AddMonoid`-valued `f`. -/
def sumMap {α β : Type} [AddMonoid α] (f : β → α) : List β → α
  | [] => 0
  | x :: xs => f x + sumMap f xs

@[simp] theorem sumMap_nil {α β : Type} [AddMonoid α] (f : β → α) : sumMap f [] = 0 := rfl

@[simp] theorem sumMap_cons {α β : Type} [AddMonoid α] (f : β → α) (x : β) (xs : List β) :
    sumMap f (x :: xs) = f x + sumMap f xs := rfl

@[simp] theorem sumMap_singleton {α β : Type} [AddMonoid α] (f : β → α) (x : β) :
    sumMap f [x] = f x := by simp

/-- `sumMap` distributes over list append. -/
@[simp]
theorem sumMap_append {α β : Type} [AddMonoid α] (f : β → α) (l₁ l₂ : List β) :
    sumMap f (l₁ ++ l₂) = sumMap f l₁ + sumMap f l₂ := by
  induction l₁ with
  | nil => simp [sumMap]
  | cons x xs ih => simp [sumMap, ih, add_assoc]

/-- `sumBy` for `Nat` is a specialization of `sumMap`. -/
theorem sumBy_eq_sumMap {β : Type} (f : β → Nat) (xs : List β) : sumBy f xs = sumMap f xs := by
  induction xs with
  | nil => simp [sumBy, sumMap]
  | cons x xs ih => simp [sumBy, sumMap, ih]

/-- If `f x ≤ g x` pointwise, then the sum over any list respects that order. -/
theorem sumBy_le_sumBy {β : Type} (f g : β → Nat)
    (h : ∀ x, f x ≤ g x) : ∀ xs : List β, sumBy f xs ≤ sumBy g xs
  | [] => by simp
  | x :: xs => by
      simp [sumBy]
      exact Nat.add_le_add (h x) (sumBy_le_sumBy f g h xs)

/-- Sum a list of natural numbers. -/
def listSum : List Nat → Nat := sumBy id

@[simp] theorem listSum_nil : listSum [] = 0 := rfl

@[simp] theorem listSum_cons (x : Nat) (xs : List Nat) :
    listSum (x :: xs) = x + listSum xs := rfl

@[simp] theorem listSum_singleton (x : Nat) : listSum [x] = x := by
  simp [listSum]

/-- Sum over an empty list truncated to n is zero. -/
theorem sumBy_take_nil {β : Type} (f : β → Nat) (n : Nat) :
    sumBy f (List.take n []) = 0 := by
  cases n <;> rfl

/-- Sum is invariant under permutation of the list. -/
theorem sumBy_perm {β : Type} (f : β → Nat) {l₁ l₂ : List β}
    (h : Perm l₁ l₂) :
    sumBy f l₁ = sumBy f l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sumBy, ih]
  | swap x y l => simp [sumBy, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Sorting by descending score does not change the sum. -/
theorem sumBy_sortByDescending {β : Type} (f : β → Nat) (l : List β) :
    sumBy f (sortByDescending f l) = sumBy f l := by
  exact sumBy_perm f
    (perm_insertionSort (fun a b : β => f b ≤ f a) l)

/-- `sumBy` distributes over list append. -/
@[simp]
theorem sumBy_append {β : Type} (f : β → Nat) (l₁ l₂ : List β) :
    sumBy f (l₁ ++ l₂) = sumBy f l₁ + sumBy f l₂ := by
  induction l₁ with
  | nil => simp [sumBy]
  | cons x xs ih => simp [sumBy, ih, Nat.add_assoc]

/-- `listSum` distributes over list append. -/
@[simp]
theorem listSum_append (xs ys : List Nat) :
    listSum (xs ++ ys) = listSum xs + listSum ys :=
  sumBy_append id xs ys

/-- Sum of a list of naturals is preserved by descending sort. -/
theorem listSum_sortDesc (l : List Nat) : listSum (sortDesc l) = listSum l := by
  exact sumBy_sortByDescending id l

/-- The sum of `Nat`-valued scores is non-negative. -/
theorem zero_le_sumBy {β : Type} (f : β → Nat) (xs : List β) : 0 ≤ sumBy f xs :=
  Nat.zero_le _

/-- The sum of a list of naturals is non-negative. -/
theorem zero_le_listSum (xs : List Nat) : 0 ≤ listSum xs :=
  zero_le_sumBy id xs

/-! ## Sum over replicated values -/

/-- `sumBy` over a replicated list: `sumBy f (replicate n x) = n * f x`. -/
theorem sumBy_replicate {β : Type} (f : β → Nat) (n : Nat) (x : β) :
    sumBy f (replicate n x) = n * f x := by
  induction n with
  | zero => simp [sumBy]
  | succ n ih =>
      rw [replicate_succ]
      simp [sumBy, ih, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- `listSum` over a replicated list: `listSum (replicate n x) = n * x`. -/
theorem listSum_replicate (n x : Nat) : listSum (replicate n x) = n * x :=
  sumBy_replicate id n x

/-! ## Sum of sublists (take / drop) -/

/-- The sum of the first `n` elements of a list is at most the sum of the whole list. -/
theorem listSum_take_le (n : Nat) (xs : List Nat) : listSum (xs.take n) ≤ listSum xs := by
  induction n generalizing xs with
  | zero =>
      cases xs <;> simp [listSum, sumBy]
  | succ n ih =>
      cases xs with
      | nil => simp [listSum, sumBy]
      | cons x xs =>
          simp [listSum, sumBy]
          exact ih xs

/-- The sum of the elements after dropping the first `n` elements is at most the sum of the
whole list. -/
theorem listSum_drop_le (n : Nat) (xs : List Nat) : listSum (xs.drop n) ≤ listSum xs := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil => simp [listSum, sumBy]
      | cons x xs =>
          exact Nat.le_trans (ih xs) (Nat.le_add_left (listSum xs) x)

/-! ## Monotonicity under mapping -/

/-- Sum is monotone with respect to adding a constant to each element:
`listSum xs ≤ listSum (xs.map fun x => x + c)`. -/
theorem listSum_le_listSum_map_add (c : Nat) : (xs : List Nat) → listSum xs ≤ listSum (xs.map fun x => x + c)
  | [] => by simp [listSum, sumBy]
  | x :: xs => by
      simp [listSum, sumBy]
      exact Nat.add_le_add (Nat.le_add_right x c) (listSum_le_listSum_map_add c xs)

/-! ## Sum over a range of natural numbers -/

/-- Sum `f i` for `i` from `0` to `n-1`. Equivalent to `sumBy f (range n)`. -/
def rangeSum (n : Nat) (f : Nat → Nat) : Nat :=
  sumBy f (range n)

@[simp] theorem rangeSum_zero (f : Nat → Nat) : rangeSum 0 f = 0 := by
  simp [rangeSum]

theorem rangeSum_succ (n : Nat) (f : Nat → Nat) :
    rangeSum (n + 1) f = f n + rangeSum n f := by
  simp [rangeSum, sumBy_append, range_succ, sumBy_singleton, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-! ## Sum with a fixed first argument -/

/-- Sum a binary scoring function `score : α → β → Nat` over a list of `β` values,
keeping the first argument `a : α` fixed. Equivalent to `sumBy (score a) xs`. -/
def sumWith {α β : Type} (score : α → β → Nat) (a : α) : List β → Nat
  | [] => 0
  | b :: bs => score a b + sumWith score a bs

@[simp] theorem sumWith_nil {α β : Type} (score : α → β → Nat) (a : α) :
    sumWith score a [] = 0 := rfl

@[simp] theorem sumWith_cons {α β : Type} (score : α → β → Nat) (a : α)
    (b : β) (bs : List β) :
    sumWith score a (b :: bs) = score a b + sumWith score a bs := rfl

/-- `sumWith` distributes over list append. -/
theorem sumWith_append {α β : Type} (score : α → β → Nat)
    (a : α) (xs ys : List β) :
    sumWith score a (xs ++ ys) = sumWith score a xs + sumWith score a ys := by
  induction xs with
  | nil => simp [sumWith]
  | cons x xs ih => simp [sumWith, ih, Nat.add_assoc]

/-- `sumWith` over a reversed list equals `sumWith` over the original list. -/
theorem sumWith_reverse {α β : Type} (score : α → β → Nat)
    (a : α) (xs : List β) :
    sumWith score a xs.reverse = sumWith score a xs := by
  induction xs with
  | nil => simp [sumWith]
  | cons x xs ih =>
      simp [sumWith, sumWith_append, ih]
      omega

/-- If all scores are zero, the sum is zero. -/
theorem sumWith_eq_zero_of_forall {α β : Type} {score : α → β → Nat}
    {a : α} :
    ∀ xs : List β, (∀ b ∈ xs, score a b = 0) → sumWith score a xs = 0
  | [], _ => by simp [sumWith]
  | b :: bs, h => by
      have hb : score a b = 0 := h b (by simp)
      have hbs : ∀ c ∈ bs, score a c = 0 := by
        intro c hc; exact h c (by simp [hc])
      simp [sumWith, hb, sumWith_eq_zero_of_forall bs hbs]

/-! ## Modular sum fold -/

/-- Fold over `xs`, summing `f x` values modulo `modulus`.
The fold accumulates `(acc + f x) % modulus` left-to-right, starting from `0`. -/
def sumModWith {α : Type} (modulus : Nat) (xs : List α) (f : α → Nat) : Nat :=
  xs.foldl (fun acc x => (acc + f x) % modulus) 0

@[simp] theorem sumModWith_nil {α : Type} (modulus : Nat) (f : α → Nat) :
    sumModWith modulus [] f = 0 := rfl

private lemma foldl_mod_step_lt {α : Type} (modulus : Nat) (hpos : 0 < modulus)
    (xs : List α) (f : α → Nat) (init : Nat) (hinit : init < modulus) :
    xs.foldl (fun acc x => (acc + f x) % modulus) init < modulus := by
  revert init
  induction xs with
  | nil => exact fun _ h => h
  | cons x xs ih =>
      intro init hinit
      have hstep : (init + f x) % modulus < modulus := Nat.mod_lt _ hpos
      exact ih _ hstep

/-- `sumModWith` result is always less than the modulus (when `modulus > 0`). -/
theorem sumModWith_lt_modulus {α : Type} (modulus : Nat) (xs : List α) (f : α → Nat)
    (hpos : 0 < modulus) : sumModWith modulus xs f < modulus := by
  unfold sumModWith
  apply foldl_mod_step_lt modulus hpos xs f 0
  exact hpos

/-- If all `f x` are zero, `sumModWith` returns zero. -/
theorem sumModWith_eq_zero_of_forall {α : Type} (modulus : Nat) (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x = 0) : sumModWith modulus xs f = 0 := by
  induction xs with
  | nil => simp [sumModWith]
  | cons x xs ih =>
      have hx : f x = 0 := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := by
        intro y hy; exact h y (by simp [hy])
      rw [sumModWith, List.foldl_cons, hx]
      simp
      rw [← sumModWith]
      exact ih hxs

/-! ## Standard library `List.sum` lemmas -/

/-- Sum of a list of `n` ones equals `n`. -/
theorem sum_replicate_one (n : Nat) : List.sum (List.replicate n 1) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.sum_cons]
      rw [ih]
      omega

/-- If every element of `xs` is `1`, then `List.sum xs` equals `xs.length`. -/
theorem sum_eq_length_of_all_one {xs : List Nat}
    (h : ∀ x ∈ xs, x = 1) : List.sum xs = xs.length := by
  have hrep : xs = List.replicate xs.length 1 :=
    List.eq_replicate_iff.mpr ⟨rfl, h⟩
  rw [hrep]
  simp [sum_replicate_one]

/-- If every element of `xs` is `0`, then `List.sum xs` equals `0`. -/
theorem sum_eq_zero_of_forall_eq_zero {xs : List Nat}
    (h : ∀ x ∈ xs, x = 0) : List.sum xs = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x = 0 := h x (by simp)
      have hxs : ∀ y ∈ xs, y = 0 := by
        intro y hy; exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- If every element of `xs` is `≤ 1`, then the sum of `xs` is at most its length.
Together with `sum_eq_length_of_all_one`, this captures the key property that a list
of binary values has sum bounded by length. -/
theorem sum_le_length_of_forall_le_one {xs : List Nat}
    (h : ∀ x ∈ xs, x ≤ 1) : List.sum xs ≤ List.length xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ 1 := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ 1 := by
        intro y hy; exact h y (by simp [hy])
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_le_add hx (ih hxs)

/-- If every element of `flags` is binary (i.e., `0` or `1`), then the sum is at most
the length. A specialization of `sum_le_length_of_forall_le_one`. -/
theorem sum_le_length_of_binary {flags : List Nat}
    (h : ∀ f ∈ flags, f = 0 ∨ f = 1) : List.sum flags ≤ List.length flags :=
  sum_le_length_of_forall_le_one fun f hf =>
    Nat.le_one_of_eq_zero_or_one (h f hf)

/-- Sum of `f x + c` over a list equals the sum of `f x` plus `length • c`.
This is a specialized form of `List.sum_map_add` where the second function is constant. -/
theorem sum_map_add_const [AddCommMonoid α] (l : List β) (f : β → α) (c : α) :
    (l.map fun x => f x + c).sum = (l.map f).sum + l.length • c := by
  simp [List.sum_map_add, List.map_const, List.sum_replicate]

/-! ## Sum of filtered positive elements -/

/-- The sum of all positive elements in a list of `Int`s is nonnegative. -/
theorem sum_filter_pos_nonneg (xs : List Int) :
    0 ≤ (xs.filter (fun x => x > 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x > 0
      · have hsum : 0 ≤ x + (xs.filter (fun x => x > 0)).sum := by
          have hx_nonneg : 0 ≤ x := le_of_lt hx
          linarith
        simpa [decide_eq_true hx] using hsum
      · simpa [decide_eq_false hx] using ih

/-! ## Map and permutation lemmas for `sumMap` -/

/-- `sumMap` distributes over `List.map`: `sumMap g (xs.map f) = sumMap (g ∘ f) xs`. -/
theorem sumMap_map {α β γ : Type} [AddMonoid α] (f : β → γ) (g : γ → α) (xs : List β) :
    sumMap g (xs.map f) = sumMap (g ∘ f) xs := by
  induction xs with
  | nil => simp [sumMap]
  | cons x xs ih => simp [sumMap, ih]

/-- `sumMap` is invariant under permutation of the list. -/
theorem sumMap_eq_of_perm {α β : Type} [AddCommMonoid α] (f : β → α) {l₁ l₂ : List β}
    (h : l₁.Perm l₂) : sumMap f l₁ = sumMap f l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sumMap, ih]
  | swap x y l => simp [sumMap, add_assoc, add_comm, add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `sumMap` is equivalent to `List.sum` applied to the mapped list. -/
theorem sumMap_eq_list_sum_map {α β : Type} [AddMonoid α] (f : β → α) (xs : List β) :
    sumMap f xs = List.sum (xs.map f) := by
  induction xs with
  | nil => simp [sumMap]
  | cons x xs ih => simp [sumMap, List.sum_cons, ih]

/-! ## `sumSnd`: sum second components of pairs

`sumSnd zero [(a₁, b₁), ..., (aₙ, bₙ)] = zero + b₁ + ... + bₙ`.
This is the `foldl`-based sum of the second components of a list of pairs with
an explicit starting value. Related to `sumMap Prod.snd` but does not require
`AddMonoid` — only `Add` and an explicit `zero`. -/

/-- Sum the second components of a list of pairs, starting from `zero`.
`sumSnd zero [(a₁, b₁), (a₂, b₂)] = zero + b₁ + b₂`. -/
def sumSnd {α β : Type} [Add β] (zero : β) (items : List (α × β)) : β :=
  items.foldl (fun acc p => acc + p.2) zero

/-! ## `all` equivalence theorems

`xs.all p` is `true` iff every element of `xs` satisfies `p` (in the `Bool` sense),
and `false` iff some element does not satisfy `p`. These are the fundamental
soundness and completeness lemmas for `List.all`. -/

/-- If every element of `xs` satisfies `p`, then `xs.all p = true`. -/
theorem all_eq_true_of_forall_mem {α : Type u} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : xs.all p = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : p x = true := h x (by simp)
      have hxs : ∀ y ∈ xs, p y = true := by
        intro y hy; exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- If `xs.all p = true`, then every element of `xs` satisfies `p`. -/
theorem forall_mem_of_all_eq_true {α : Type u} {p : α → Bool} {xs : List α}
    (h : xs.all p = true) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro x hx; simp at hx
  | cons x xs ih =>
      cases hx : p x with
      | false => simp [hx] at h
      | true =>
          have hxs : xs.all p = true := by
            simpa [hx] using h
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hx
          · exact ih hxs y hy

/-- `xs.all p = true` iff every element of `xs` satisfies `p`. -/
theorem all_eq_true_iff {α : Type u} {p : α → Bool} {xs : List α} :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true :=
  ⟨forall_mem_of_all_eq_true, all_eq_true_of_forall_mem⟩

/-- If there exists an element of `xs` for which `p` returns `false`,
then `xs.all p = false`. -/
theorem all_eq_false_of_exists_not {α : Type u} {p : α → Bool} {xs : List α}
    (h : ∃ x ∈ xs, p x = false) : xs.all p = false := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rcases h with ⟨y, hy, hp⟩
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp [hp]
      · simp [ih ⟨y, hy, hp⟩]

/-- If `xs.all p = false`, then there exists an element on which `p` returns `false`. -/
theorem exists_false_of_all_eq_false {α : Type u} {p : α → Bool} {xs : List α}
    (h : xs.all p = false) : ∃ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases hx : p x with
      | false => exact ⟨x, by simp, hx⟩
      | true =>
          have hxs : xs.all p = false := by
            simpa [hx] using h
          rcases ih hxs with ⟨y, hy, hp⟩
          exact ⟨y, by simp [hy], hp⟩

/-- `xs.all p = false` iff there exists an element on which `p` returns `false`. -/
theorem all_eq_false_iff {α : Type u} {p : α → Bool} {xs : List α} :
    xs.all p = false ↔ ∃ x ∈ xs, p x = false :=
  ⟨exists_false_of_all_eq_false, all_eq_false_of_exists_not⟩

/-! ## `all` with `DecidablePred` (Prop predicates)

These lemmas handle `List.all` when the predicate is `α → Prop` with `[DecidablePred p]`,
bridging the gap between the Prop and Bool worlds. -/

/-- If `∀ x, p x → q x` and all elements of `xs` satisfy `p`, then they all satisfy `q`.
This is the monotonicity / implication lemma for `List.all` with `DecidablePred`. -/
theorem all_of_all_imp {α : Type u} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ x, p x → q x) {xs : List α} (h : xs.all p) :
    xs.all q := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have hp : p x := of_decide_eq_true (h x hx)
  simpa using himp x hp

/-! ## Contradiction lemmas for `all` -/

/-- A nonempty list cannot satisfy both `all p` and `all (fun x => decide (¬ p x))`.
That is, it is impossible for `all` to return true for both a predicate and its
boolean negation when the list has at least one element. -/
theorem not_all_and_all_not_of_nonempty
    {α : Type u} {p : α → Bool} {xs : List α}
    (hne : ∃ x, x ∈ xs)
    (hp : xs.all p)
    (hnp : xs.all (fun x => decide (¬ p x))) : False := by
  rcases hne with ⟨x, hx⟩
  have hp_true : p x = true := (all_eq_true_iff.mp hp) x hx
  have hp_not_dec : decide (¬ p x) = true := (all_eq_true_iff.mp hnp) x hx
  have hp_not : ¬ p x := of_decide_eq_true hp_not_dec
  exact hp_not hp_true

end List

end Specific
