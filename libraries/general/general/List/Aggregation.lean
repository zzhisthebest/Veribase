import Mathlib
import general.Finite.Core
import general.List.Transformations

namespace List

/-! ### `listSum` — sum of a `List Nat` yielding `Int` -/

/-- Sum of a list of natural numbers, yielding an integer.
Equivalent to `(l.map Int.ofNat).sum`. -/
def listSum (l : List Nat) : Int := (l.map Int.ofNat).sum

lemma listSum_nil : listSum ([] : List Nat) = 0 := rfl

lemma listSum_foldl_add (b : Int) (l : List Nat) :
    l.foldl (fun acc n => acc + (Int.ofNat n : Int)) b = b + listSum l := by
  induction l generalizing b with
  | nil => simp [listSum]
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp [listSum, add_assoc]

lemma listSum_cons (x : Nat) (xs : List Nat) :
    listSum (x :: xs) = (x : Int) + listSum xs := by
  simp [listSum]

/-! ### `appendAll` — concatenate a list of values via `Append` -/

/-- Concatenate a list of values via `Append`, starting from the `Inhabited` default
(the empty element). For `String` this is `""`, so `appendAll ["a","b"] = "ab"`.
For `List α` this is `[]`. -/
def appendAll {α : Type u} [Append α] [Inhabited α] (ws : List α) : α :=
  ws.foldl (· ++ ·) default


lemma appendAll_nil {α : Type u} [Append α] [Inhabited α] : appendAll ([] : List α) = default := by
  simp [appendAll]

/-! ### `sumZipped` — sum of a pairwise-zipped function over two lists -/

/-- Sum of `f aᵢ bᵢ` for pairwise zipped elements of two lists. -/
def sumZipped {α β : Type} (f : α → β → Nat) (as : List α) (bs : List β) : Nat :=
  (List.zip as bs).foldl (fun acc (a, b) => acc + f a b) 0

/-- `sumZipped` decomposes at the head of both lists. -/
lemma sumZipped_cons {α β : Type} (f : α → β → Nat) (a : α) (b : β) (as : List α) (bs : List β) :
    sumZipped f (a :: as) (b :: bs) = f a b + sumZipped f as bs := by
  have shift (l : List (α × β)) (n : Nat) :
      l.foldl (fun acc p => acc + f p.1 p.2) n =
        n + l.foldl (fun acc p => acc + f p.1 p.2) 0 := by
    induction l generalizing n with
    | nil => simp
    | cons p ps ih => simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih (f p.1 p.2)]; omega
  simpa [sumZipped] using shift (List.zip as bs) (f a b)

/-- `sumZipped f as bs = (zipWith f as bs).sum` — the two formulations coincide. -/
lemma sumZipped_eq_zipWith_sum {α β : Type} (f : α → β → Nat) (as : List α) (bs : List β) :
    sumZipped f as bs = (List.zipWith f as bs).sum := by
  induction as generalizing bs with
  | nil => simp [sumZipped]
  | cons a as ih =>
    cases bs with
    | nil => simp [sumZipped]
    | cons b bs => simp [sumZipped_cons, ih, List.zipWith]

/-- Monotonicity of `sumZipped (fun a b => b - a)` in the second list:
if `bs` and `cs` have the same length as `as`, and for every position `i`,
`bs.getD i 0 ≤ cs.getD i 0`, then the cost from `as` to `bs` is ≤ the cost to `cs`.
This captures the core monotonicity used in greedy "make-strictly-increasing" style problems. -/
lemma sumZipped_sub_mono (as bs cs : List Nat)
    (h_len_bs : bs.length = as.length) (h_len_cs : cs.length = as.length)
    (h_le : ∀ i, i < as.length → bs.getD i 0 ≤ cs.getD i 0) :
    sumZipped (fun a b => b - a) as bs ≤ sumZipped (fun a b => b - a) as cs := by
  induction as generalizing bs cs with
  | nil => simp [sumZipped]
  | cons a as ih =>
    cases bs with
    | nil => simp at h_len_bs
    | cons b bs' =>
      cases cs with
      | nil => simp at h_len_cs
      | cons c cs' =>
        have h_len_bs' : bs'.length = as.length := by simpa using h_len_bs
        have h_len_cs' : cs'.length = as.length := by simpa using h_len_cs
        have h_bc : b ≤ c := by
          have h0 := h_le 0 (by simp)
          simpa using h0
        have h_le' : ∀ i, i < as.length → bs'.getD i 0 ≤ cs'.getD i 0 := by
          intro i hi
          have h := h_le (i + 1) (by simp; omega)
          simpa using h
        have h_sub : (b - a) ≤ (c - a) := Nat.sub_le_sub_right h_bc a
        have ih_res := ih bs' cs' h_len_bs' h_len_cs' h_le'
        simp [sumZipped_cons]
        exact Nat.add_le_add h_sub ih_res

/-! ### `sumOver` — sum of a binary function with a fixed first argument -/

/-- Sum of `f a x` for a fixed `a` over all `x` in `xs`.
`sumOver f a xs = ∑_{x ∈ xs} f a x`. -/
def sumOver {α β : Type} (f : α → β → Nat) (a : α) (xs : List β) : Nat :=
  xs.foldl (fun acc x => acc + f a x) 0

/-- `sumOver` is equivalent to `(xs.map (f a)).sum`. -/
lemma sumOver_eq_map_sum {α β : Type} (f : α → β → Nat) (a : α) (xs : List β) :
    sumOver f a xs = (xs.map (f a)).sum := by
  have aux (l : List β) (n : Nat) :
      l.foldl (fun acc x => acc + f a x) n = n + (l.map (f a)).sum := by
    induction l generalizing n with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih, Nat.add_assoc]
  simpa [sumOver] using aux xs 0

/-- Summing over an empty list yields `0`. -/

lemma sumOver_nil {α β : Type} (f : α → β → Nat) (a : α) : sumOver f a [] = 0 := rfl

/-- Summing over `x :: xs` decomposes as `f a x + sumOver f a xs`. -/
lemma sumOver_cons {α β : Type} (f : α → β → Nat) (a : α) (x : β) (xs : List β) :
    sumOver f a (x :: xs) = f a x + sumOver f a xs := by
  rw [sumOver_eq_map_sum, sumOver_eq_map_sum]
  simp

/-! ### `sumBy` — sum of a mapped function over a list -/

/-- Sum of `f x` over all elements `x` of a list.
`sumBy f l = ∑_{x ∈ l} f x`. -/
def sumBy {β : Type} (f : β → Nat) (l : List β) : Nat :=
  l.foldl (fun acc x => acc + f x) 0


theorem sumBy_nil {β : Type} (f : β → Nat) : sumBy f [] = 0 := rfl

/-- `sumBy` over a singleton list reduces to the function applied to the element. -/

lemma sumBy_singleton {β : Type} (f : β → Nat) (x : β) : sumBy f [x] = f x := by
  simp [sumBy]

/-- `sumBy` over `x :: xs` decomposes as `f x + sumBy f xs`. -/
lemma sumBy_cons {β : Type} (f : β → Nat) (x : β) (xs : List β) : sumBy f (x :: xs) = f x + sumBy f xs := by
  have aux (l : List β) (n : Nat) :
      l.foldl (fun acc x => acc + f x) n = n + (l.map f).sum := by
    induction l generalizing n with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih, Nat.add_assoc]
  simp [sumBy, List.foldl, aux]

/-! ### `length_eq_sum_of_map_const_one` — length equals sum when all map to 1 -/

/-- When every element of a list maps to `1` under `f`, the length of the list
equals the sum of `f` applied to each element. -/
lemma length_eq_sum_of_map_const_one {α : Type} (f : α → Nat) (l : List α)
    (h : ∀ a ∈ l, f a = 1) : l.length = (l.map f).sum := by
  induction' l with x xs ih
  · simp
  · have hx : f x = 1 := h x (by simp)
    have hxs : ∀ a ∈ xs, f a = 1 := λ a ha => h a (by simp [ha])
    calc
      (x :: xs).length = xs.length + 1 := by simp
      _ = (xs.map f).sum + 1 := by rw [ih hxs]
      _ = 1 + (xs.map f).sum := by omega
      _ = f x + (xs.map f).sum := by rw [hx]
      _ = ((x :: xs).map f).sum := by simp

/-! ### `sumSnd` — sum the second components of a list of pairs -/

/-- Sum the second components of a list of pairs.
`sumSnd xs = ∑_{(_,b) ∈ xs} b`. Generalized to any `AddMonoid β`,
so it works for `Int`, `Nat`, `ℚ`, `ℝ`, etc. -/
def sumSnd {α β : Type} [AddMonoid β] (xs : List (α × β)) : β :=
  xs.foldl (fun acc kv => acc + kv.snd) 0

theorem sumSnd_nil {α β : Type} [AddMonoid β] : sumSnd ([] : List (α × β)) = 0 := rfl

end List


namespace List

/-- `sumPos l` sums the non-negative elements of a list of `Int`,
returning a `Nat`. Each non-negative value `x` contributes `x.toNat`;
negative values contribute `0`. -/
def sumPos : List Int → Nat
  | [] => 0
  | x :: xs => (if 0 ≤ x then x.toNat else 0) + sumPos xs

/-- If `l₁` is a sublist of `l₂`, then `sumPos l₁ ≤ sumPos l₂`.
Every non-negative element that contributes to `sumPos l₁` also contributes
to `sumPos l₂` when `l₁ <+ l₂`. -/
lemma sumPos_sublist {l₁ l₂ : List Int} (h : l₁ <+ l₂) : sumPos l₁ ≤ sumPos l₂ := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    dsimp [sumPos]
    by_cases ha : 0 ≤ a
    · simp [ha]; omega
    · simp [ha]; omega
  | cons₂ a h ih =>
    dsimp [sumPos]
    by_cases ha : 0 ≤ a
    · simp [ha]; omega
    · simp [ha]; omega

end List

namespace List


/-! ### `avgNat` — integer average of a list of natural numbers -/

/-- Integer average (floor division) of a list of natural numbers.
Returns `default` if the list is empty, otherwise computes `l.sum / l.length`. -/
def avgNat (default : Nat) (l : List Nat) : Nat :=
  if l.length = 0 then default
  else l.sum / l.length

theorem avgNat_nil (d : Nat) : avgNat d [] = d := by
  simp [avgNat]

theorem avgNat_singleton (d n : Nat) : avgNat d [n] = n := by
  simp [avgNat]

/-- Convenience alias for `avgNat 0`. Integer average (floor division) of a list of natural
numbers, returning `0` for the empty list. -/
def avg (l : List Nat) : Nat := avgNat 0 l

theorem avg_singleton (n : Nat) : avg [n] = n := by
  simp [avg, avgNat]

theorem avg_nil : avg [] = 0 := by
  simp [avg, avgNat]

/-- For a nonempty list, `avg` is the sum divided by the length. -/
theorem avg_eq_div_of_ne_nil {l : List Nat} (h : l ≠ []) : avg l = l.sum / l.length := by
  rcases List.exists_cons_of_ne_nil h with ⟨x, xs, rfl⟩
  simp [avg, avgNat]

/-! ### `avgNatRound` — rounded integer average of a list of natural numbers

Unlike `avgNat` (floor division), `avgNatRound` uses banker's rounding:
`(sum + len / 2) / len`, which rounds to the nearest integer, rounding up on ties. -/

/-- Rounded integer average (banker's rounding) of a list of natural numbers.
Returns `0` for the empty list, otherwise `(ns.sum + ns.length / 2) / ns.length`. -/
def avgNatRound (ns : List Nat) : Nat :=
  match ns.length with
  | 0 => 0
  | len => (ns.sum + len / 2) / len

theorem avgNatRound_nil : avgNatRound [] = 0 := rfl



/-! ### Average of a list of `Nat`

Uses natural-number (truncating) division: for nonempty lists, computes `xs.sum / xs.length`;
returns `0` for the empty list. This is the discrete counterpart of `Finset.mean`. -/

/-- Average of a list of natural numbers using truncating division.
For the empty list, returns `0`. For a nonempty list `xs`, returns `xs.sum / xs.length`. -/
def averageNat (xs : List Nat) : Nat :=
  if h : xs.length = 0 then 0 else xs.sum / xs.length


theorem averageNat_nil : averageNat [] = 0 := rfl


end List

namespace List

/-! ### Suffix sum — sum of elements from index `i` to the end of a list -/

/-- Prefix sum: the sum of the first `n` elements of `l`.
Returns `0` for the empty list or when `n = 0`. Complementary to `suffixSum`. -/
def prefixSum {α : Type u} [AddCommMonoid α] (l : List α) (n : Nat) : α :=
  (l.take n).sum

/-- The prefix sum of the first `n+1` elements of `h :: t` equals `h` plus the prefix sum
of the first `n` elements of `t`. -/
lemma prefixSum_cons {α : Type u} [AddCommMonoid α] (h : α) (t : List α) (n : Nat) :
    prefixSum (h :: t) (n + 1) = h + prefixSum t n := by
  unfold prefixSum; simp

/-- Sum of `f` applied to the first `i+1` elements of `l`.
This is a convenience wrapper: `prefixSumMap f l i = prefixSum (l.map f) (i+1)`,
or equivalently `prefixSumMap f l i = (l.take (i+1)).foldl (fun s x => s + f x) 0`. -/
def prefixSumMap {α : Type} (f : α → Nat) (l : List α) (i : Nat) : Nat :=
  prefixSum (l.map f) (i + 1)

lemma prefixSumMap_empty {α : Type} (f : α → Nat) (i : Nat) : prefixSumMap f [] i = 0 := by
  unfold prefixSumMap prefixSum; simp

/-! ### Prefix sums as a list of all running totals

These produce the full sequence of running totals, as opposed to `prefixSum`
which returns a single sum at a given index. They are thin wrappers around
`List.scanl (· + ·)`. -/

/-- Running totals (prefix sums) of a list including the initial accumulator `a`.
For example, `prefixSumsAux [1,2,3] 0 = [0,1,3,6]`.
Equivalent to `List.scanl (· + ·) a l`. -/
def prefixSumsAux {α : Type} [Add α] : List α → α → List α :=
  flip (List.scanl (· + ·))

/-- Prefix sums of a list, starting from the additive identity `0`.
For example, `prefixSums [1,2,3] = [0,1,3,6]`.
Equivalent to `List.scanl (· + ·) 0`. -/
def prefixSums {α : Type} [AddMonoid α] (xs : List α) : List α :=
  xs.scanl (· + ·) 0

/-- Sum of elements in `l` from index `i` to the end (suffix sum). -/
def suffixSum {α : Type} [AddCommMonoid α] (l : List α) (i : Nat) : α :=
  List.sum (l.drop i)

/-- Suffix sum of an empty list is always zero. -/

lemma suffixSum_nil {α : Type} [AddCommMonoid α] (i : Nat) : suffixSum ([] : List α) i = 0 := by
  simp [suffixSum]

end List


namespace List

/-- `filterProduct l₁ l₂ p` returns the list of all pairs `(a, b)` where `a ∈ l₁`, `b ∈ l₂`,
and the boolean predicate `p a b` holds. It is the cartesian product `l₁ × l₂` filtered by `p`. -/
def filterProduct {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Bool) : List (α × β) :=
  (List.product l₁ l₂).filter (fun (a, b) => p a b)

/-- If a pair `x` is in `filterProduct l₁ l₂ p`, then `p x.1 x.2` is true and both components
belong to their respective lists. -/
lemma mem_filterProduct {α β : Type} {l₁ : List α} {l₂ : List β} {p : α → β → Bool} {x : α × β}
    (hx : x ∈ filterProduct l₁ l₂ p) : (p x.1 x.2 = true) ∧ x.1 ∈ l₁ ∧ x.2 ∈ l₂ := by
  unfold filterProduct at hx
  rw [List.mem_filter] at hx
  rcases hx with ⟨hm, hp⟩
  have hprod := (List.mem_product.mp hm)
  rcases hprod with ⟨ha, hb⟩
  exact ⟨by simpa using hp, ha, hb⟩

/-- Every pair in `filterProduct l₁ l₂ p` satisfies the predicate `p` and has components
in their respective lists. This is the `List.Forall` version of `mem_filterProduct`. -/
lemma forall_filterProduct {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Bool) :
    List.Forall (fun (x : α × β) => p x.1 x.2 = true ∧ x.1 ∈ l₁ ∧ x.2 ∈ l₂) (filterProduct l₁ l₂ p) := by
  rw [List.forall_iff_forall_mem]
  intro x hx
  exact mem_filterProduct hx

/-! ### Products of triples of distinct elements -/

/-- Given a list `numbers` with a multiplication, compute the Finset of all products
`numbers.get i * numbers.get j * numbers.get k` where `i`, `j`, `k` are pairwise
distinct indices (any order). This enumerates all P(n,3) = n·(n-1)·(n-2) ordered
triple products with distinct positions. -/
def tripleProducts [Mul α] [DecidableEq α] (numbers : List α) : Finset α :=
  let n := numbers.length
  (Fin.distinctTriples n).image (λ ⟨i, j, k⟩ => numbers.get i * numbers.get j * numbers.get k)

/-- If the list has at least 3 elements, then `tripleProducts numbers` is nonempty. -/
lemma tripleProducts_nonempty [Mul α] [DecidableEq α] (numbers : List α) (h : numbers.length ≥ 3) :
    (tripleProducts numbers).Nonempty := by
  unfold tripleProducts
  have hne : (Fin.distinctTriples numbers.length).Nonempty :=
    Fin.distinctTriples_nonempty numbers.length h
  rcases hne with ⟨⟨i, j, k⟩, hmem⟩
  refine ⟨numbers.get i * numbers.get j * numbers.get k, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(i, j, k), hmem, rfl⟩

end List

namespace List

/-! ### Maximum product complement -/

/-- Given a list of values and a total, compute the maximum of `x * (total - x)`
over all `x` in the list. Returns `0` for the empty list.

This is useful for problems that involve splitting a total into two parts
and maximizing the product of the two parts, e.g., maximizing `s * (total - s)`
over all candidate `s` values. -/
def maxProdComplement : List Nat → Nat → Nat
  | [], _ => 0
  | s :: xs, total =>
      let prod := s * (total - s)
      let bestRest := maxProdComplement xs total
      if prod > bestRest then prod else bestRest


lemma maxProdComplement_nil {total : Nat} : maxProdComplement [] total = 0 := rfl

lemma maxProdComplement_cons (s : Nat) (xs : List Nat) (total : Nat) :
    maxProdComplement (s :: xs) total =
      let prod := s * (total - s)
      let bestRest := maxProdComplement xs total
      if prod > bestRest then prod else bestRest := rfl

end List


namespace List

/-! ### Index-wise sum over a range with a weight function -/

/-- For each index `i` from `0` to `n-1`, sum `weight i j` over all `j` from `0` to `n-1`
where predicate `p j` holds. Returns a list of length `n`.
This is a general-purpose combinator for problems involving pairwise distance/weight sums
between indices, such as computing the sum of distances from each position to all positions
satisfying a condition. -/
def sumIdxWhere (weight : Nat → Nat → Nat) (n : Nat) (p : Nat → Bool) : List Nat :=
  (List.range n).map (fun i =>
    List.sum ((List.range n).map (fun j =>
      if p j then weight i j else 0)))

/-- For each index `i` of `cs`, sum `Nat.dist i j` over all indices `j`
where `p (cs[j])` holds. Generalized over any inhabited type and predicate.
This is a specialization of `sumIdxWhere` using `Nat.dist` as the weight
and reading the predicate from list elements via `cs[j]!`. -/
def sumDistToIndicesWhere {α : Type} [Inhabited α] (cs : List α) (p : α → Bool) : List Nat :=
  sumIdxWhere Nat.dist cs.length (fun j => p (cs[j]!))

end List

namespace List

/-! # Mode finding by scanning candidates

This module provides functions and theorems for finding the mode (most frequent
element) of a list by scanning through candidate elements. The core idea is a
comparison function `betterMode` that picks the better of two elements as a mode
candidate, and `foldMode` that folds this comparison over a candidate list.

Contrast with `maxByFreq` and `modes` in `general.List.Count`, which work on
deduplicated lists and use `Option` for the result. This module works directly
with the raw list as candidates and uses a simpler fold-based approach.
-/

variable {α : Type} [DecidableEq α] [LinearOrder α]

/-! ### `betterMode` — compare two elements as mode candidates -/

/-- Given a list `l` and two elements `a` and `b`, return the one that is a
"better" candidate for the mode of `l`: higher count in `l` wins; if counts are
equal, the smaller element wins (using `min`).

This is the comparison step used in mode-finding by scanning. -/
def betterMode (l : List α) (a b : α) : α :=
  if l.count a > l.count b then a
  else if l.count a = l.count b then min a b
  else b

/-! ### Membership property of `betterMode` -/

/-- If both `a` and `b` belong to `numbers`, then `betterMode numbers a b`
also belongs to `numbers`. This is the key invariant that lets us fold
`betterMode` over candidates while staying within the original list. -/
lemma betterMode_mem (numbers : List α) (a b : α) (ha : a ∈ numbers) (hb : b ∈ numbers) :
    betterMode numbers a b ∈ numbers := by
  unfold betterMode
  split
  · exact ha
  · split
    · by_cases hle : a ≤ b
      · have hmin : min a b = a := min_eq_left hle
        rw [hmin]
        exact ha
      · have hmin : min a b = b := min_eq_right (le_of_lt (lt_of_not_ge hle))
        rw [hmin]
        exact hb
    · exact hb

/-! ### `foldMode` — scan candidates keeping the best mode so far -/

/-- Scan through `candidates` (which should all be in `numbers`), keeping
`best` as the best mode-so-far. At each step, use `betterMode` to compare
the new candidate against the current best, and keep the winner.

This is the core recursion of mode-finding-by-scanning. The final mode is
obtained by calling `foldMode numbers numbers (head numbers)`. -/
def foldMode (numbers : List α) (candidates : List α) (best : α) : α :=
  match candidates with
  | [] => best
  | x :: xs => foldMode numbers xs (betterMode numbers x best)

/-! ### `countCmp` — compare elements by count descending, then by value

This section provides a `Bool` comparator that orders elements by their count in a
reference list (descending), with tie-breaking by the elements' natural `≤` order.
When a list is sorted by `countCmp xs`, its head is the mode (most frequent element)
of `xs`, and if there are ties, the head is the smallest element among the most frequent. -/

/-- Comparator: `a` precedes `b` if `a` has a higher count in `xs`, or same count but `a ≤ b`.
This makes the most frequent element (and smallest among ties) the "least" element.
Sort by `countCmp xs` to bring the mode to the front. -/
def countCmp (xs : List α) (a b : α) : Bool :=
  let ca := List.count a xs
  let cb := List.count b xs
  ca > cb || (ca = cb && a ≤ b)

/-- `countCmp xs a b` is equivalent to `count a xs ≥ count b xs`, and if counts are equal then `a ≤ b`. -/
lemma countCmp_iff (xs : List α) (a b : α) :
    countCmp xs a b = true ↔
    (List.count a xs ≥ List.count b xs) ∧
    (List.count a xs = List.count b xs → a ≤ b) := by
  simp [countCmp]
  constructor
  · intro h
    rcases h with (hcnt | ⟨hcnt, hle⟩)
    · constructor
      · exact Nat.le_of_lt hcnt
      · intro heq; exfalso
        rw [heq] at hcnt
        exact Nat.lt_irrefl _ hcnt
    · constructor
      · rw [hcnt]
      · intro; exact hle
  · intro ⟨hge, himp⟩
    by_cases hcnt : List.count a xs > List.count b xs
    · exact Or.inl hcnt
    · have heq : List.count a xs = List.count b xs :=
        Nat.le_antisymm (Nat.le_of_not_gt hcnt) hge
      exact Or.inr ⟨heq, himp heq⟩

/-- If a nonempty list is sorted by `countCmp xs` and is a permutation of `xs`,
its head is the mode element of `xs`: it belongs to `xs` and its count is ≥ every other
element's count, with the smallest element among ties. -/
lemma head_of_countSorted_is_mode
    (xs : List α) (h : α) (t : List α)
    (h_perm : (h :: t).Perm xs)
    (h_sorted : List.Pairwise (fun a b => countCmp xs a b = true) (h :: t)) :
    h ∈ xs ∧ (∀ y, y ∈ xs → (List.count h xs ≥ List.count y xs ∧
      (List.count h xs = List.count y xs → h ≤ y))) := by
  rcases List.pairwise_cons.mp h_sorted with ⟨h_head_rel, h_tail_pairwise⟩
  have h_mem : h ∈ xs := by
    have : h ∈ (h :: t) := by simp
    exact h_perm.mem_iff.mp this
  have h_mode_prop : ∀ y, y ∈ xs → ((List.count h xs ≥ List.count y xs) ∧
      (List.count h xs = List.count y xs → h ≤ y)) := by
    intro y hy
    have hy_sorted : y ∈ (h :: t) := h_perm.mem_iff.mpr hy
    simp at hy_sorted
    rcases hy_sorted with (hy_eq | hy_tail)
    · rw [hy_eq]
      exact ⟨le_rfl, fun _ => le_rfl⟩
    · have h_cmp : countCmp xs h y = true := h_head_rel y hy_tail
      exact (countCmp_iff xs h y).mp h_cmp
  exact ⟨h_mem, h_mode_prop⟩

/-! ### `modeBest` — recursive mode-finding with carried count

`modeBest` is an alternative to `foldMode` that carries the current best count
along as an explicit parameter, avoiding recounting the best candidate at each step.
The invariants maintained are:
- `bestVal ∈ orig` with `bestCnt = orig.count bestVal`
- Every element `y ∈ orig` not yet considered (not in `candidates`) has count that
  either is strictly less than `bestCnt`, or equals `bestCnt` with `bestVal ≤ y`.

When `candidates` is empty, `bestVal` is the mode (highest count, ties to smallest). -/

/-- Iterate through `candidates` (a nodup list of elements from `orig`),
maintaining the best element seen so far (`bestVal`) with its count (`bestCnt`).
Returns the element with the highest count in `orig`, breaking ties by smallest value. -/
def modeBest (candidates : List α) (orig : List α) (bestVal : α) (bestCnt : Nat) : α :=
  match candidates with
  | [] => bestVal
  | x :: xs =>
    let c := orig.count x
    if bestCnt < c ∨ (bestCnt = c ∧ x < bestVal) then
      modeBest xs orig x c
    else
      modeBest xs orig bestVal bestCnt

/-- When there are no more candidates to check, the current best element `bestVal`
is the mode: it belongs to `orig`, its count is maximal, and it is minimal among
elements achieving that count. -/
lemma modeBest_nil_spec (orig : List α) (bestVal : α) (bestCnt : Nat)
    (h_mem : bestVal ∈ orig)
    (h_cnt : bestCnt = orig.count bestVal)
    (h_inv : ∀ y ∈ orig, orig.count y < bestCnt ∨ (orig.count y = bestCnt ∧ bestVal ≤ y)) :
    bestVal ∈ orig ∧
    (∀ n ∈ orig, orig.count n ≤ orig.count bestVal) ∧
    (∀ n ∈ orig, orig.count n = orig.count bestVal → bestVal ≤ n) := by
  have h_ge : ∀ n ∈ orig, orig.count n ≤ orig.count bestVal := by
    intro n hn
    have h := h_inv n hn
    rcases h with (hlt | ⟨heq, _⟩)
    · omega
    · omega
  have h_le : ∀ n ∈ orig, orig.count n = orig.count bestVal → bestVal ≤ n := by
    intro n hn heq
    have h := h_inv n hn
    rcases h with (hlt | ⟨heq', hle⟩)
    · omega
    · exact hle
  exact ⟨h_mem, h_ge, h_le⟩

/-- Main correctness theorem for `modeBest`: given a nodup list of candidates that
are all in `orig`, an initial best candidate in `orig` with correct count, and the
invariant that all elements not in candidates have counts bounded by the current
best, the result of `modeBest` is an element of `orig` whose count is maximal and
which is minimal among elements achieving that maximum count. -/
lemma modeBest_correct (candidates : List α) (orig : List α) (bestVal : α) (bestCnt : Nat)
    (h_mem : bestVal ∈ orig)
    (h_cnt : bestCnt = orig.count bestVal)
    (h_sub : ∀ y ∈ candidates, y ∈ orig)
    (h_nodup : candidates.Nodup)
    (h_inv : ∀ y ∈ orig, y ∉ candidates → orig.count y < bestCnt ∨ (orig.count y = bestCnt ∧ bestVal ≤ y)) :
    modeBest candidates orig bestVal bestCnt ∈ orig ∧
    (∀ n ∈ orig, orig.count n ≤ orig.count (modeBest candidates orig bestVal bestCnt)) ∧
    (∀ n ∈ orig, orig.count n = orig.count (modeBest candidates orig bestVal bestCnt) →
      modeBest candidates orig bestVal bestCnt ≤ n) := by
  induction' candidates with x xs ih generalizing bestVal bestCnt
  · -- base case: candidates = []
    simp [modeBest, h_cnt]
    apply modeBest_nil_spec orig bestVal bestCnt h_mem h_cnt
    intro y hy
    exact h_inv y hy (by simp)
  · -- inductive case: candidates = x :: xs
    have hx_mem : x ∈ orig := h_sub x (by simp)
    have hx_nin_xs : x ∉ xs := (List.nodup_cons.mp h_nodup).left
    have h_nodup_xs : xs.Nodup := (List.nodup_cons.mp h_nodup).right
    simp [modeBest]
    by_cases h_beat : bestCnt < orig.count x ∨ (bestCnt = orig.count x ∧ x < bestVal)
    · -- x beats bestVal: update best to x
      simp [h_beat]
      have h_inv' : ∀ y ∈ orig, y ∉ xs → orig.count y < orig.count x ∨ (orig.count y = orig.count x ∧ x ≤ y) := by
        intro y hy hy_nin_xs
        by_cases hy_eq_x : y = x
        · rw [hy_eq_x]
          right; exact ⟨rfl, le_rfl⟩
        · have hy_nin_cand : y ∉ x :: xs := by
            simp [hy_eq_x, hy_nin_xs]
          have h_old := h_inv y hy hy_nin_cand
          rcases h_old with (hlt | ⟨heq, hle⟩)
          · rcases h_beat with (hlt_b | ⟨heq_b, hlt_b⟩)
            · left; omega
            · left; omega
          · rcases h_beat with (hlt_b | ⟨heq_b, hlt_b⟩)
            · left; omega
            · right
              exact ⟨heq.trans heq_b, le_trans (le_of_lt hlt_b) hle⟩
      have h_sub' : ∀ y ∈ xs, y ∈ orig := by
        intro y hy; exact h_sub y (by simp [hy])
      apply ih
      · exact hx_mem
      · rfl
      · exact h_sub'
      · exact h_nodup_xs
      · exact h_inv'
    · -- x does NOT beat bestVal: keep bestVal
      simp [h_beat]
      have h_not_beat : ¬ (bestCnt < orig.count x ∨ (bestCnt = orig.count x ∧ x < bestVal)) := h_beat
      have h_x_ge_or_lt : orig.count x < bestCnt ∨ (orig.count x = bestCnt ∧ bestVal ≤ x) := by
        by_cases h_eq : orig.count x = bestCnt
        · have : ¬ (x < bestVal) := by
            intro hxlt; apply h_not_beat; right; exact ⟨h_eq.symm, hxlt⟩
          right; exact ⟨h_eq, le_of_not_gt this⟩
        · left; omega
      have h_inv' : ∀ y ∈ orig, y ∉ xs → orig.count y < bestCnt ∨ (orig.count y = bestCnt ∧ bestVal ≤ y) := by
        intro y hy hy_nin_xs
        by_cases hy_eq_x : y = x
        · rw [hy_eq_x]
          exact h_x_ge_or_lt
        · have hy_nin_cand : y ∉ x :: xs := by
            simp [hy_eq_x, hy_nin_xs]
          exact h_inv y hy hy_nin_cand
      have h_sub' : ∀ y ∈ xs, y ∈ orig := by
        intro y hy; exact h_sub y (by simp [hy])
      apply ih
      · exact h_mem
      · exact h_cnt
      · exact h_sub'
      · exact h_nodup_xs
      · exact h_inv'

/-! ### `mode` — compute the mode element of a list -/

/-- Return the mode (most frequent element) of a list, with ties broken by smallest value.
Returns `none` iff the list is empty.

Contrast with `maxByFreq` in `general.List.Count` which breaks ties by *largest* element,
and `foldMode` which does not handle the empty case. -/
def mode (numbers : List α) : Option α :=
  match numbers with
  | [] => none
  | x :: _ =>
    some (modeBest (numbers.dedup) numbers x (numbers.count x))

end List
