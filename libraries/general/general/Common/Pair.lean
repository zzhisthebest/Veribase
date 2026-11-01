import Mathlib

/-! ### Lexicographic order on product types

This module defines `pairLE` and `LexDesc`, two lexicographic ordering relations on `α × β`, and
provides `IsTrans`, `IsTotal`, and `DecidableRel` typeclass instances when `α` and `β` are `LinearOrder`.
Useful for `List.Sorted` and `List.insertionSort` with pair orderings.

`pairLE` sorts by first component ascending, then by second component ascending.
`LexDesc` sorts by second component descending, then by first component ascending.

Contrast with `Nat.pair_le` (in `general/Nat.lean`) which is specialized to `Nat × Nat`. -/

/-- Lexicographic order on `α × β`: `(a, b) ≤ (c, d)` iff `a < c` or `(a = c ∧ b ≤ d)`.
This is a `Prop`-valued relation suitable for `List.Sorted` and typeclass instances. -/
def pairLE {α β : Type} [LT α] [DecidableEq α] [LE β] (p q : α × β) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- `pairLE` is transitive when `α` and `β` are `LinearOrder`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTrans (α × β) pairLE :=
  ⟨by
    intro a b c hab hbc
    rcases hab with (hlt | ⟨heq, hle⟩)
    · rcases hbc with (hlt' | ⟨heq', hle'⟩)
      · exact Or.inl (lt_trans hlt hlt')
      · exact Or.inl (by rw [← heq']; exact hlt)
    · rcases hbc with (hlt' | ⟨heq', hle'⟩)
      · exact Or.inl (by rw [heq]; exact hlt')
      · exact Or.inr ⟨heq.trans heq', le_trans hle hle'⟩⟩

/-- `pairLE` is total when `α` and `β` are `LinearOrder`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTotal (α × β) pairLE :=
  ⟨by
    intro a b
    by_cases hlt : a.1 < b.1
    · exact Or.inl (Or.inl hlt)
    · by_cases hlt' : b.1 < a.1
      · exact Or.inr (Or.inl hlt')
      · have heq : a.1 = b.1 := le_antisymm (le_of_not_gt hlt') (le_of_not_gt hlt)
        by_cases hle : a.2 ≤ b.2
        · exact Or.inl (Or.inr ⟨heq, hle⟩)
        · have hle' : b.2 ≤ a.2 := le_of_lt (lt_of_not_ge hle)
          exact Or.inr (Or.inr ⟨heq.symm, hle'⟩)⟩

/-- `pairLE` is decidable when the component types have `LinearOrder`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : DecidableRel (pairLE (α := α) (β := β)) := by
  intro p q; unfold pairLE; infer_instance

/-! ### `fstLE` — compare pairs by first component only -/

/-- Compare two pairs by their first component only: `fstLE a b` iff `a.1 ≤ b.1`.
This is a total preorder (reflexive, transitive, total) but not antisymmetric —
pairs with equal first components are considered equivalent regardless of the
second component. Suitable for `List.insertionSort` when you want to sort by key
alone, ignoring tied keys (stable sort preserves original order among ties).

Contrast with `pairLE` which breaks ties by comparing the second component. -/
def fstLE {α β : Type} [LE α] (a b : α × β) : Prop := a.1 ≤ b.1

/-- `fstLE` is decidable when `α` is a `LinearOrder`. -/
instance {α β : Type} [LinearOrder α] : DecidableRel (fstLE (α := α) (β := β)) := by
  intro a b; dsimp [fstLE]; infer_instance

/-- `fstLE` is total when `α` is a `LinearOrder`. -/
instance {α β : Type} [LinearOrder α] : IsTotal (α × β) fstLE :=
  ⟨fun a b => by
    dsimp [fstLE]
    exact le_total a.1 b.1⟩

/-- `fstLE` is transitive when `α` has `IsTrans (· ≤ ·)`. -/
instance {α β : Type} [Preorder α] : IsTrans (α × β) fstLE :=
  ⟨fun a b c hab hbc => by
    dsimp [fstLE] at hab hbc ⊢
    exact le_trans hab hbc⟩

/-! ### `sndGE` — compare pairs by second component descending -/

/-- Compare two pairs by their second component descending: `sndGE a b` iff `a.snd ≥ b.snd`.
This is the second-component descending dual of `fstLE`. Suitable for `List.insertionSort`
when you want to sort pairs by value in descending order, ignoring the first component. -/
def sndGE {α β : Type _} [LE β] (a b : α × β) : Prop := a.snd ≥ b.snd

/-- `sndGE` is decidable when `β` has a decidable `≥` relation. -/
instance {α β : Type _} [LE β] [DecidableRel (· ≥ · : β → β → Prop)] : DecidableRel (sndGE (α := α) (β := β)) :=
  fun a b => inferInstanceAs (Decidable (a.snd ≥ b.snd))

/-- `sndGE` is transitive when `β` is a `Preorder`. -/
instance {α β : Type _} [Preorder β] : IsTrans (α × β) (sndGE (α := α) (β := β)) where
  trans a b c h1 h2 := by
    simp [sndGE] at h1 h2 ⊢
    exact ge_trans h1 h2

/-- `sndGE` is total when `β` is a `LinearOrder`. -/
instance {α β : Type _} [LinearOrder β] : IsTotal (α × β) (sndGE (α := α) (β := β)) where
  total a b := by
    simp [sndGE]
    exact le_total _ _

/-- If a list is `Pairwise` under `sndGE`, then the second components are non-increasing
by index: earlier entries have `≥` second component. -/
lemma pairwise_sndGE_get {α β : Type _} [LE β] {l : List (α × β)}
    (h : List.Pairwise (sndGE (α := α) (β := β)) l)
    (i j : Fin l.length) (hij : i < j) :
    (l.get i).snd ≥ (l.get j).snd := by
  have h_pw_get := (List.pairwise_iff_get.mp h) i j hij
  unfold sndGE at h_pw_get
  exact h_pw_get

/-! ### `compareSndDesc` — `Bool` comparator by second component descending

`compareSndDesc` is the `Bool`-valued counterpart of `sndGE`. While `sndGE` is a `Prop`
relation with `DecidableRel`/`IsTrans`/`IsTotal` instances suitable for `List.insertionSort`,
`compareSndDesc` is a `Bool` comparator suitable for `List.mergeSort` and other
`Bool`-based sorting APIs. -/

/-- `compareSndDesc a b` returns `true` iff `a.snd ≥ b.snd`.
This is the `Bool`-valued counterpart of `sndGE`, suitable for `List.mergeSort`. -/
def compareSndDesc {α β : Type} [LinearOrder β] (a b : α × β) : Bool :=
  decide (a.2 ≥ b.2)

/-- `compareSndDesc` is transitive: if `a.snd ≥ b.snd` and `b.snd ≥ c.snd`, then `a.snd ≥ c.snd`.
Needed as a hypothesis for `List.sorted_mergeSort`. -/
lemma compareSndDesc_trans {α β : Type} [LinearOrder β] (a b c : α × β) :
    compareSndDesc a b = true → compareSndDesc b c = true → compareSndDesc a c = true := by
  unfold compareSndDesc
  intro h1 h2
  have h1' : b.2 ≤ a.2 := of_decide_eq_true h1
  have h2' : c.2 ≤ b.2 := of_decide_eq_true h2
  have h3' : c.2 ≤ a.2 := le_trans h2' h1'
  exact decide_eq_true h3'

/-- If a list of pairs is `Pairwise` ordered by `compareSndDesc`, then for any `i < j`
(as `Fin` indices), the second component at index `i` is ≥ the second component at index `j`.

This is the `Bool`/`Pairwise` counterpart of `pairwise_sndGE_get`. -/
lemma pairwise_compareSndDesc_get {α β : Type} [LinearOrder β]
    {L : List (α × β)} (h_sorted : List.Pairwise (fun a b => compareSndDesc a b = true) L)
    {i j : Fin L.length} (h_lt : i.1 < j.1) : (L.get i).2 ≥ (L.get j).2 := by
  have h := (List.pairwise_iff_get.mp h_sorted) i j h_lt
  unfold compareSndDesc at h
  exact of_decide_eq_true h

/-- For any list of `α × β` where `β` is a linear order, `insertionSort` with `sndGE`
produces a permutation whose second components are non-increasing by index. -/
lemma insertionSort_sndGE_spec {α β : Type _} [LinearOrder β] (l : List (α × β)) :
    List.Perm l (List.insertionSort (sndGE (α := α) (β := β)) l) ∧
    (∀ i j (hi : i < (List.insertionSort (sndGE (α := α) (β := β)) l).length)
      (hj : j < (List.insertionSort (sndGE (α := α) (β := β)) l).length)
      (hij : i < j),
      ((List.insertionSort (sndGE (α := α) (β := β)) l).get ⟨i, hi⟩).snd ≥
      ((List.insertionSort (sndGE (α := α) (β := β)) l).get ⟨j, hj⟩).snd) := by
  let result := List.insertionSort (sndGE (α := α) (β := β)) l
  have h_perm : List.Perm l result :=
    (List.perm_insertionSort (sndGE (α := α) (β := β)) l).symm
  have h_sorted : List.Sorted (sndGE (α := α) (β := β)) result :=
    List.sorted_insertionSort (sndGE (α := α) (β := β)) l
  have h_pairwise : List.Pairwise (sndGE (α := α) (β := β)) result := h_sorted
  have h_ge : ∀ i j (hi : i < result.length) (hj : j < result.length) (hij : i < j),
      (result.get ⟨i, hi⟩).snd ≥ (result.get ⟨j, hj⟩).snd := by
    intro i j hi hj hij
    simpa using pairwise_sndGE_get h_pairwise ⟨i, hi⟩ ⟨j, hj⟩ hij
  exact And.intro h_perm h_ge

/-! ### `sndLE` — compare pairs by second component ascending -/

/-- Compare two pairs by their second component ascending: `sndLE a b` iff `a.snd ≤ b.snd`.
This is the second-component ascending dual of `sndGE`. Suitable for `List.insertionSort`
when you want to sort pairs by value in ascending order, ignoring the first component.

Contrast with `sndGE` (descending) and `fstLE` (compare by first component). -/
def sndLE {α β : Type _} [LE β] (a b : α × β) : Prop := a.snd ≤ b.snd

/-- `sndLE` is decidable when `β` has a decidable `≤` relation. -/
instance {α β : Type _} [LE β] [DecidableRel (· ≤ · : β → β → Prop)] : DecidableRel (sndLE (α := α) (β := β)) :=
  fun a b => inferInstanceAs (Decidable (a.snd ≤ b.snd))

/-- `sndLE` is transitive when the underlying `≤` on `β` is transitive. -/
instance {α β : Type _} [LE β] [IsTrans β (· ≤ ·)] : IsTrans (α × β) (sndLE (α := α) (β := β)) where
  trans a b c h₁ h₂ := by
    dsimp [sndLE] at h₁ h₂ ⊢
    exact IsTrans.trans (α := β) (a := a.snd) (b := b.snd) (c := c.snd) h₁ h₂

/-- `sndLE` is total when the underlying `≤` on `β` is total. -/
instance {α β : Type _} [LE β] [IsTotal β (· ≤ ·)] : IsTotal (α × β) (sndLE (α := α) (β := β)) where
  total a b := by
    dsimp [sndLE]
    exact IsTotal.total (α := β) (a.snd) (b.snd)

/-- If a list of pairs is sorted by `sndLE`, then the relation holds between
elements at ordered indices: for `i < j < xs.length`, `sndLE (xs[i]!) (xs[j]!)`.
This bridges `List.Sorted` with `getElem!`-style indexing for `sndLE`-sorted lists. -/
lemma sorted_sndLE_getElem!_of_lt {α β : Type _} [LE β] [Inhabited (α × β)]
    (xs : List (α × β)) (h_sorted : List.Sorted sndLE xs) (i j : Nat) (hij : i < j) (hj : j < xs.length) :
    sndLE (xs[i]!) (xs[j]!) := by
  have hi : i < xs.length := Nat.lt_trans hij hj
  have hrel := h_sorted.rel_get_of_lt (Fin.mk_lt_mk.mpr hij : (⟨i, hi⟩ : Fin xs.length) < ⟨j, hj⟩)
  simpa [sndLE, getElem!_pos xs i hi, getElem!_pos xs j hj] using hrel

/-! ### `LexDesc` — lexicographic order descending by second component -/

/-- Lexicographic-like total order on product types: first by the second component descending,
then by the first component ascending. This is the reflexive (≤) version needed for
`List.insertionSort`. -/
def LexDesc {α β : Type} [LinearOrder α] [LinearOrder β] (a b : α × β) : Prop :=
  a.2 > b.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)

/-- Decidability of `LexDesc`, inherited from the `LinearOrder` instances. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : DecidableRel (LexDesc (α:=α) (β:=β)) := by
  intro a b
  dsimp [LexDesc]
  infer_instance

/-- Transitivity of `LexDesc`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTrans (α × β) (LexDesc (α:=α) (β:=β)) where
  trans a b c h₁ h₂ := by
    rcases h₁ with (h₁ | ⟨h₁eq, h₁le⟩)
    · -- a.2 > b.2
      rcases h₂ with (h₂ | ⟨h₂eq, h₂le⟩)
      · -- b.2 > c.2
        left; exact lt_trans h₂ h₁
      · -- b.2 = c.2 ∧ b.1 ≤ c.1
        left; rw [h₂eq] at h₁; exact h₁
    · -- a.2 = b.2 ∧ a.1 ≤ b.1
      rcases h₂ with (h₂ | ⟨h₂eq, h₂le⟩)
      · -- b.2 > c.2
        left; simpa [h₁eq] using h₂
      · -- b.2 = c.2 ∧ b.1 ≤ c.1
        right; rw [h₁eq, h₂eq]; exact ⟨rfl, le_trans h₁le h₂le⟩

/-- Totality of `LexDesc`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTotal (α × β) (LexDesc (α:=α) (β:=β)) where
  total a b := by
    dsimp [LexDesc]
    by_cases h : a.2 > b.2
    · exact Or.inl (Or.inl h)
    · have hnge : a.2 ≤ b.2 := le_of_not_gt h
      by_cases hl : a.2 < b.2
      · exact Or.inr (Or.inl hl)
      · have heq : a.2 = b.2 := le_antisymm hnge (le_of_not_gt hl)
        by_cases hs : a.1 ≤ b.1
        · exact Or.inl (Or.inr ⟨heq, hs⟩)
        · have hbs : b.1 ≤ a.1 := le_of_not_ge hs
          exact Or.inr (Or.inr ⟨heq.symm, hbs⟩)

/-! ### `Sorted_LexDesc_to_target` — convert LexDesc sorted to strict target order -/

/-- Convert `Sorted LexDesc` (non-strict total order) to the strict target order,
using the fact that all first components are distinct (from Nodup). -/
lemma Sorted_LexDesc_to_target {α β : Type} [LinearOrder α] [LinearOrder β]
    (l : List (α × β)) (h_sorted : List.Sorted (LexDesc (α:=α) (β:=β)) l)
    (h_nodup : List.Nodup (l.map Prod.fst)) :
    List.Sorted (fun a b => a.2 > b.2 ∨ (a.2 = b.2 ∧ a.1 < b.1)) l := by
  induction h_sorted with
  | nil => exact List.Pairwise.nil
  | @cons a l_tl h h_tl ih =>
    -- h : ∀ a' ∈ l_tl, LexDesc a a'
    -- Need: ∀ a' ∈ l_tl, target a a'  and  Pairwise target l_tl
    have h_nodup_cons : List.Nodup (a.1 :: (l_tl.map Prod.fst)) := by
      simpa [List.map_cons] using h_nodup
    rcases List.nodup_cons.mp h_nodup_cons with ⟨h_a1_not_mem, h_nodup_tl⟩
    have h_target : ∀ a' ∈ l_tl, (a.2 > a'.2 ∨ (a.2 = a'.2 ∧ a.1 < a'.1)) := by
      intro a' ha'
      have h_cmp : LexDesc (α:=α) (β:=β) a a' := h a' ha'
      rcases h_cmp with (hgt | ⟨heq, hle⟩)
      · left; exact hgt
      · -- a.2 = a'.2 ∧ a.1 ≤ a'.1; need a.1 < a'.1
        have h_a1_ne_a'1 : a.1 ≠ a'.1 := by
          intro heq_str
          apply h_a1_not_mem
          rw [List.mem_map]
          exact ⟨a', ha', heq_str.symm⟩
        have h_a1_lt_a'1 : a.1 < a'.1 := lt_of_le_of_ne hle h_a1_ne_a'1
        right; exact ⟨heq, h_a1_lt_a'1⟩
    refine List.Pairwise.cons h_target ?_
    apply ih
    simpa [List.map_cons] using h_nodup_tl

/-! ### `sorted_pairLE_map_snd_property` — bridge `pairLE`-sorted to function-ordered projection -/

/-- If a list of `(β × α)` pairs is sorted by `pairLE` and each first component
equals some function `f` applied to the second component, then the list of second
components (when accessed by increasing indices) satisfies the ordering property:
for `i < j`, either `f(wᵢ) < f(wⱼ)` or `f(wᵢ) = f(wⱼ)` with `wᵢ ≤ wⱼ`. -/
lemma sorted_pairLE_map_snd_property {α β : Type} [LinearOrder α] [LinearOrder β]
    (xs : List (β × α)) (f : α → β)
    (h_sorted : List.Sorted pairLE xs)
    (h_count : ∀ p ∈ xs, p.1 = f p.2)
    (i j : Nat) (hi : i < (xs.map Prod.snd).length) (hj : j < (xs.map Prod.snd).length)
    (hij : i < j) :
    f ((xs.map Prod.snd).get ⟨i, hi⟩) < f ((xs.map Prod.snd).get ⟨j, hj⟩) ∨
    (f ((xs.map Prod.snd).get ⟨i, hi⟩) = f ((xs.map Prod.snd).get ⟨j, hj⟩) ∧
     (xs.map Prod.snd).get ⟨i, hi⟩ ≤ (xs.map Prod.snd).get ⟨j, hj⟩) := by
  have h_len_map : (xs.map Prod.snd).length = xs.length := by simp
  have hi_sorted : i < xs.length := by
    rw [← h_len_map]; exact hi
  have hj_sorted : j < xs.length := by
    rw [← h_len_map]; exact hj
  let fi : Fin xs.length := ⟨i, hi_sorted⟩
  let fj : Fin xs.length := ⟨j, hj_sorted⟩
  have h_fi_lt_fj : fi < fj := hij
  have h_rel : pairLE (xs.get fi) (xs.get fj) :=
    h_sorted.rel_get_of_lt h_fi_lt_fj
  unfold pairLE at h_rel
  have h_get_i : (xs.map Prod.snd).get ⟨i, hi⟩ = (xs.get fi).2 := by
    dsimp [fi]; simp
  have h_get_j : (xs.map Prod.snd).get ⟨j, hj⟩ = (xs.get fj).2 := by
    dsimp [fj]; simp
  have h_mem_fi : xs.get fi ∈ xs := by simp
  have h_mem_fj : xs.get fj ∈ xs := by simp
  have h_eq_i : (xs.get fi).1 = f ((xs.get fi).2) := h_count (xs.get fi) h_mem_fi
  have h_eq_j : (xs.get fj).1 = f ((xs.get fj).2) := h_count (xs.get fj) h_mem_fj
  rcases h_rel with (h_lt | ⟨h_eq_nat, h_le⟩)
  · left
    rw [h_get_i, h_get_j, ← h_eq_i, ← h_eq_j]
    exact h_lt
  · right
    rw [h_get_i, h_get_j, ← h_eq_i, ← h_eq_j]
    exact ⟨h_eq_nat, h_le⟩

/-! ### `LexAsc` — lexicographic order ascending by second component

This is the ascending dual of `LexDesc`. `LexAsc a b` holds iff `a.2 < b.2`, or `a.2 = b.2`
and `a.1 ≤ b.1`. Together with `LexDesc`, `pairLE`, `fstLE`, and `sndGE`, this covers
the most common lexicographic pair orderings.

Contrast:
- `LexAsc` sorts by second component **ascending**, then first ascending.
- `LexDesc` sorts by second component **descending**, then first ascending.
- `pairLE` sorts by first component ascending, then second ascending. -/

/-- Lexicographic order on product types: first by the second component ascending,
then by the first component ascending.
`LexAsc a b` holds iff `a.2 < b.2`, or `a.2 = b.2` and `a.1 ≤ b.1`.

Suitable for `List.insertionSort` and `List.Sorted`. -/
def LexAsc {α β : Type} [LinearOrder α] [LinearOrder β] (a b : α × β) : Prop :=
  a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)

/-- Decidability of `LexAsc`, inherited from the `LinearOrder` instances. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : DecidableRel (LexAsc (α := α) (β := β)) := by
  intro a b
  unfold LexAsc
  infer_instance

/-- Transitivity of `LexAsc`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTrans (α × β) (LexAsc (α := α) (β := β)) where
  trans a b c hab hbc := by
    unfold LexAsc at hab hbc ⊢
    rcases hab with (hlt | ⟨heq, hle⟩)
    · rcases hbc with (hlt' | ⟨heq', hle'⟩)
      · exact Or.inl (lt_trans hlt hlt')
      · exact Or.inl (by simpa [heq'] using hlt)
    · rcases hbc with (hlt' | ⟨heq', hle'⟩)
      · exact Or.inl (by simpa [heq] using hlt')
      · exact Or.inr ⟨by rw [heq, heq'], le_trans hle hle'⟩

/-- Totality of `LexAsc`. -/
instance {α β : Type} [LinearOrder α] [LinearOrder β] : IsTotal (α × β) (LexAsc (α := α) (β := β)) where
  total a b := by
    unfold LexAsc
    by_cases hlt : a.2 < b.2
    · exact Or.inl (Or.inl hlt)
    · have hle_ab : b.2 ≤ a.2 := le_of_not_gt hlt
      rcases lt_or_eq_of_le hle_ab with (hlt' | heq)
      · exact Or.inr (Or.inl hlt')
      · by_cases hle_fst : a.1 ≤ b.1
        · exact Or.inl (Or.inr ⟨heq.symm, hle_fst⟩)
        · have hle_fst' : b.1 ≤ a.1 := le_of_not_ge hle_fst
          exact Or.inr (Or.inr ⟨heq, hle_fst'⟩)

/-! ### `pairwise_sndGE_iff_get` — bidirectional index characterization

`pairwise_sndGE_get` gives the forward direction: `Pairwise sndGE` implies `.snd`
is non-increasing by index. This lemma adds the reverse direction, giving a full
`↔` characterization. -/

/-- `List.Pairwise` with `sndGE` is equivalent to the condition that later elements
have `.snd` ≤ earlier elements' `.snd`. This is the bidirectional version of
`pairwise_sndGE_get`. -/
lemma pairwise_sndGE_iff_get {α β : Type _} [LE β] (l : List (α × β)) :
    List.Pairwise (sndGE (α := α) (β := β)) l ↔
    ∀ (i j : Fin l.length), i.1 < j.1 → (l.get j).snd ≤ (l.get i).snd := by
  constructor
  · exact pairwise_sndGE_get
  · intro h
    apply List.pairwise_iff_get.mpr
    intro i j hij
    have h' := h i j hij
    unfold sndGE
    exact h'

/-! ### `orderedPair` — create a sorted pair

`orderedPair a b` returns `(a, b)` if `a ≤ b`, otherwise `(b, a)`, so the first
component is always ≤ the second component. This is useful for canonicalizing
unordered pairs before comparison, e.g. representing an undirected edge as a
sorted pair. -/

/-- Create the pair `(a, b)` ordered so that the first component ≤ second component. -/
def orderedPair {α : Type u} [LinearOrder α] (a b : α) : α × α :=
  if a ≤ b then (a, b) else (b, a)

/-- The first component of `orderedPair` is ≤ the second component. -/
lemma orderedPair_fst_le_snd {α : Type u} [LinearOrder α] (a b : α) : (orderedPair a b).1 ≤ (orderedPair a b).2 := by
  dsimp [orderedPair]
  by_cases h : a ≤ b
  · simp [h]
  · have h' : b ≤ a := le_of_not_ge h
    simp [h, h']

/-! ### `squaredDist` — squared Euclidean distance in 2D -/

/-- Squared Euclidean distance between two points `p1`, `p2` in a 2D space over a ring.
`squaredDist p1 p2 = (p1.1 - p2.1)^2 + (p1.2 - p2.2)^2`.

This avoids a square root, so it works over any `Ring α` (not just `ℝ`).
Use `pairwiseMap squaredDist` to compute consecutive squared distances
along a path of points (see `List.pairwiseMap` in `general/List.lean`). -/
def squaredDist {α : Type _} [Ring α] (p1 p2 : α × α) : α :=
  let dx := p1.1 - p2.1
  let dy := p1.2 - p2.2
  dx * dx + dy * dy


namespace Pair

/-! ### `maxByFst` — pick the pair with larger first component -/

/-- Pick the larger of two pairs by their first component.
If first components are equal, the first argument is returned (ties are broken by position). -/
def maxByFst {A B : Type _} [LinearOrder A] (a b : A × B) : A × B :=
  if b.1 > a.1 then b else a

/-- `maxByFst a b` is either `a` or `b`. -/
lemma maxByFst_is_either {A B : Type _} [LinearOrder A] (a b : A × B) : maxByFst a b = a ∨ maxByFst a b = b := by
  unfold maxByFst
  split
  · right; rfl
  · left; rfl

/-- The first component of `maxByFst a b` is at least `a.1`. -/
lemma maxByFst_fst_ge {A B : Type _} [LinearOrder A] (a b : A × B) : (maxByFst a b).1 ≥ a.1 := by
  unfold maxByFst
  split
  · next h => exact le_of_lt h
  · rfl

/-! ### Folding `maxByFst` over a list -/

/-- The result of folding `maxByFst` over a list is a member of `t₀ :: ts`. -/
lemma foldl_maxByFst_mem {A B : Type _} [LinearOrder A] (t₀ : A × B) (ts : List (A × B)) :
    List.foldl maxByFst t₀ ts ∈ t₀ :: ts := by
  induction' ts with t ts ih generalizing t₀
  · exact .head _
  · have h_ih := ih (maxByFst t₀ t)
    have h_sub : (maxByFst t₀ t :: ts) ⊆ (t₀ :: t :: ts) := by
      intro x hx
      have h_cases : x = maxByFst t₀ t ∨ x ∈ ts := by
        match hx with
        | .head _ => exact Or.inl rfl
        | .tail _ h => exact Or.inr h
      rcases h_cases with (rfl | hx')
      · have h_either := maxByFst_is_either t₀ t
        rcases h_either with (h | h)
        · rw [h]; exact .head _
        · rw [h]; exact .tail _ (.head _)
      · exact .tail _ (.tail _ hx')
    have h_fold : List.foldl maxByFst t₀ (t :: ts) = List.foldl maxByFst (maxByFst t₀ t) ts := rfl
    rw [h_fold]
    exact h_sub h_ih

/-- Folding `maxByFst` gives a result whose first component dominates all first components
of elements in `t₀ :: ts`. -/
lemma foldl_maxByFst_ge {A B : Type _} [LinearOrder A] (t₀ : A × B) (ts : List (A × B))
    (s : A × B) (hs : s ∈ t₀ :: ts) :
    s.1 ≤ (List.foldl maxByFst t₀ ts).1 := by
  induction' ts with t ts ih generalizing t₀ s
  · cases hs with
    | head _ => rfl
    | tail _ h => nomatch h
  · have h_fold : List.foldl maxByFst t₀ (t :: ts) = List.foldl maxByFst (maxByFst t₀ t) ts := rfl
    rw [h_fold]
    cases hs with
    | head hs_head =>
      have h_cmp : t₀.1 ≤ (maxByFst t₀ t).1 := maxByFst_fst_ge t₀ t
      have h_ih : (maxByFst t₀ t).1 ≤ (List.foldl maxByFst (maxByFst t₀ t) ts).1 :=
        ih (maxByFst t₀ t) (maxByFst t₀ t) (.head _)
      exact le_trans h_cmp h_ih
    | tail _ hs' =>
      cases hs' with
      | head hs_head' =>
        have h_cmp_t : t.1 ≤ (maxByFst t₀ t).1 := by
          unfold maxByFst
          split
          · next _ => rfl
          · next h => exact le_of_not_gt h
        have h_ih : (maxByFst t₀ t).1 ≤ (List.foldl maxByFst (maxByFst t₀ t) ts).1 :=
          ih (maxByFst t₀ t) (maxByFst t₀ t) (.head _)
        exact le_trans h_cmp_t h_ih
      | tail _ hs'' =>
        have h_ih : s.1 ≤ (List.foldl maxByFst (maxByFst t₀ t) ts).1 :=
          ih (maxByFst t₀ t) s (.tail _ hs'')
        exact h_ih

/-! ### `pickMaxByFst` — argmax by first component -/

/-- Pick the pair with the largest first component from a list.
Returns `(default, default)` for empty lists. -/
def pickMaxByFst {A B : Type _} [LinearOrder A] [Inhabited A] [Inhabited B] (l : List (A × B)) : A × B :=
  match l with
  | [] => (default, default)
  | t :: ts => ts.foldl maxByFst t

/-- The result of `pickMaxByFst` has first component at least as large as any element in the list. -/
lemma pickMaxByFst_ge {A B : Type _} [LinearOrder A] [Inhabited A] [Inhabited B]
    {l : List (A × B)} (s : A × B) (hs : s ∈ l) :
    s.1 ≤ (pickMaxByFst l).1 := by
  unfold pickMaxByFst
  cases' l with t ts
  · simp at hs
  · exact foldl_maxByFst_ge t ts s hs

/-! ### `extremeFstValue` — extract extreme first component from list of pairs

Given a list of `(Nat × β)` pairs and a decidable comparison `cmp`,
return the "extreme" first-component value. If the list is empty, returns `init`.
Otherwise, starts with the first element's first component as the accumulator
and folds `cmp` over the remaining elements, replacing the accumulator
whenever `cmp` says the new value should win.

For example, `extremeFstValue data (· > ·) 0` gives the maximum and
`extremeFstValue data (· < ·) 0` gives the minimum first component.
Contrast with `pickMaxByFst` which returns the *full pair* with the maximum
first component, and uses `default` for empty lists. -/

/-- Fold a decidable comparison over the first components of a list of pairs.
Returns `init` for empty lists; otherwise uses the first element's first component
as the initial accumulator. -/
def extremeFstValue {β : Type u} (data : List (Nat × β)) (cmp : Nat → Nat → Prop) [DecidableRel cmp]
    (init : Nat) : Nat :=
  match data with
  | []        => init
  | (t, _)::r => r.foldl (fun m p => if cmp p.1 m then p.1 else m) t

/-- The maximum first-component value among all pairs in `data`.
Returns `0` for empty lists. -/
def maxFstValue {β : Type u} (data : List (Nat × β)) : Nat := extremeFstValue data (· > ·) 0


end Pair

namespace Pair

/-! ### `map_map_snd_eq_self` — mapping into pairs then projecting back

These lemmas connect `List.map` with pair projections, useful when constructing
`(key, value)` pairs from a list and later extracting the values. -/

/-- Mapping each element `x` to `(f x, x)` and then taking the second projection
restores the original list. -/
lemma map_map_snd_eq_self {α β : Type} (f : α → β) (xs : List α) :
    (xs.map (fun x => (f x, x))).map Prod.snd = xs := by
  rw [List.map_map]
  have h_comp : Prod.snd ∘ (fun (x : α) => (f x, x)) = id := by
    ext x; simp
  rw [h_comp, List.map_id]

/-- If a pair `(f x, x)` comes from mapping `fun x => (f x, x)` over a list,
then the first component equals `f` applied to the second component. -/
lemma fst_eq_f_snd_of_mem_map {α β : Type} (f : α → β) (xs : List α)
    (p : β × α) (hp : p ∈ xs.map (fun x => (f x, x))) : p.1 = f p.2 := by
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  simp

/-- Mapping each element `x` to `(x, f x)` and then taking the first projection
restores the original list. This is the `fst`-projection analogue of `map_map_snd_eq_self`,
where the function is placed in the second component instead of the first. -/
lemma map_map_fst_eq_self {α β : Type} (f : α → β) (xs : List α) :
    (xs.map (fun x => (x, f x))).map Prod.fst = xs := by
  rw [List.map_map]
  have hcomp : (Prod.fst ∘ fun x => (x, f x)) = id := by
    ext x; simp
  rw [hcomp, List.map_id]

/-- Mapping each element `x` to `(x, f x)` preserves the length of the list. -/
lemma length_map_mkPair {α β : Type} (f : α → β) (xs : List α) :
    (xs.map (fun x => (x, f x))).length = xs.length := by
  simp

/-- If a pair `p` comes from mapping `fun x => (x, f x)` over a list,
then the second component equals `f` applied to the first component.
This is the dual of `fst_eq_f_snd_of_mem_map` (which handles `(f x, x)` mappings). -/
lemma snd_eq_f_fst_of_mem_map {α β : Type} (f : α → β) (xs : List α)
    (p : α × β) (hp : p ∈ xs.map (fun x => (x, f x))) : p.2 = f p.1 := by
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  simp

/-! ### Uniqueness of the second component in `(x, f x)` maps

In the result of mapping `fun x => (x, f x)` over a list, the first component uniquely
determines the second component: if two pairs share the same first component, their
second components must be equal. This follows from `snd_eq_f_fst_of_mem_map`.

This is a key property for reasoning about key-value processing pipelines:
each key is associated with at most one value in such a map. -/

/-- If both `(a, b₁)` and `(a, b₂)` appear in `xs.map (fun x => (x, f x))`, then `b₁ = b₂`.
The second component is uniquely determined by the first component because each element
`x` maps to exactly one pair `(x, f x)`. -/
lemma eq_snd_of_mem_map_mkPair {α β : Type} {f : α → β} {xs : List α} {a : α} {b₁ b₂ : β}
    (h₁ : (a, b₁) ∈ xs.map (fun x => (x, f x)))
    (h₂ : (a, b₂) ∈ xs.map (fun x => (x, f x))) : b₁ = b₂ := by
  have hb₁ := snd_eq_f_fst_of_mem_map f xs (a, b₁) h₁
  have hb₂ := snd_eq_f_fst_of_mem_map f xs (a, b₂) h₂
  calc
    b₁ = f a := by simpa using hb₁
    _ = b₂ := by simpa using hb₂.symm

/-- Same as `eq_snd_of_mem_map_mkPair` but on the deduplicated list.
If both `(a, b₁)` and `(a, b₂)` appear in `(xs.dedup).map (fun x => (x, f x))`, then `b₁ = b₂`. -/
lemma eq_snd_of_mem_dedup_map_mkPair {α β : Type} [DecidableEq α] {f : α → β} {xs : List α}
    {a : α} {b₁ b₂ : β} (h₁ : (a, b₁) ∈ (xs.dedup).map (fun x => (x, f x)))
    (h₂ : (a, b₂) ∈ (xs.dedup).map (fun x => (x, f x))) : b₁ = b₂ :=
  eq_snd_of_mem_map_mkPair (by simpa [List.mem_map, List.mem_dedup] using h₁)
    (by simpa [List.mem_map, List.mem_dedup] using h₂)


end Pair

/-! ### `sumOfSnds` — sum of second components of a list of pairs

`sumOfSnds xs` sums `p.snd` for all `p ∈ xs`. For example,
`sumOfSnds [("a", 3), ("b", 5)] = 8`.
This is a convenience alias for `xs.foldl (fun acc p => acc + p.snd) 0`. -/

/-- Sum of the second (`.snd`) components of a list of `α × Nat` pairs. -/
def sumOfSnds {α : Type} (xs : List (α × Nat)) : Nat :=
  xs.foldl (fun acc p => acc + p.snd) 0

theorem sumOfSnds_nil {α : Type} : sumOfSnds ([] : List (α × Nat)) = 0 := rfl

/-! ### `filterBySnd` — filter a list of pairs by the second component

`filterBySnd pred ps` keeps only pairs `p` where `pred p.2` holds.
This generalizes `List.filter` for the common pattern of filtering pairs
by their second component. Works for any pair type `α × β`.

For example:
* `filterBySnd (· > 2) [("a", 1), ("b", 5), ("c", 3)] = [("b", 5), ("c", 3)]`
* `filterBySnd (· ≠ "") [("x", "hi"), ("y", "")] = [("x", "hi")]`
-/

/-- Filter a list of pairs by a predicate on the second component. -/
def filterBySnd {α β : Type} (pred : β → Bool) (ps : List (α × β)) : List (α × β) :=
  ps.filter (λ p => pred p.2)


lemma filterBySnd_nil {α β : Type} (pred : β → Bool) : filterBySnd pred ([] : List (α × β)) = [] := rfl

/-! ### `List.insertDesc` — insertion into a `.2`-descending list of pairs

`insertDesc` inserts an element `x : α × β` into a list sorted by the second component
in descending order. It is the pair-projection counterpart of `List.insertSortedDesc`.
Together with `List.foldl`, it provides a simple insertion-sort for key-value pairs
ordered by value (`.2`). The lemmas here prove membership, bound preservation, and
`List.Pairwise` properties.

This is similar to using `List.insertionSort` with the `sndGE` relation (defined above),
but `insertDesc` is a concrete, directly computable definition that doesn't require
a custom `DecidableRel` instance. -/

namespace List

variable {α β : Type} [LinearOrder β]

/-- Insert `x : α × β` into a list sorted by `.2` in descending order:
when the existing head `y` has `y.2 ≤ x.2`, `x` is placed before `y`. -/
def insertDesc (x : α × β) : List (α × β) → List (α × β)
| [] => [x]
| y :: ys =>
  if y.2 ≤ x.2 then
    x :: y :: ys
  else
    y :: insertDesc x ys

/-- Membership in `insertDesc x l` is equivalent to being `x` or being in `l`. -/
lemma insertDesc_mem {x p : α × β} {l : List (α × β)} :
    p ∈ insertDesc x l ↔ p = x ∨ p ∈ l := by
  induction l generalizing x p with
  | nil => simp [insertDesc]
  | cons y ys IH =>
    by_cases hcmp : y.2 ≤ x.2
    · have h_eq : insertDesc x (y :: ys) = x :: y :: ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      simp [IH, or_assoc]
    · have h_eq : insertDesc x (y :: ys) = y :: insertDesc x ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      simp [IH, or_assoc, or_comm, or_left_comm]

/-- Upper bound preservation for `insertDesc`: if `a.2` is at least `x.2` and
at least every `b.2` in `l`, then it is at least every `b.2` in `insertDesc x l`. -/
lemma insertDesc_bound {a x : α × β} {l : List (α × β)}
    (hax : a.2 ≥ x.2) (hal : ∀ b ∈ l, a.2 ≥ b.2) :
    ∀ b ∈ insertDesc x l, a.2 ≥ b.2 := by
  induction l generalizing a x with
  | nil =>
    intro b hb
    simp [insertDesc] at hb
    subst hb
    exact hax
  | cons y ys IH =>
    have hal_y : a.2 ≥ y.2 := hal y (by simp)
    have hal_ys : ∀ b ∈ ys, a.2 ≥ b.2 := by
      intro b hb
      exact hal b (by simp [hb])
    by_cases hcmp : y.2 ≤ x.2
    · have h_eq : insertDesc x (y :: ys) = x :: y :: ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      intro b hb
      simp at hb
      rcases hb with (rfl | hb')
      · exact hax
      · rcases hb' with (rfl | hb_ys)
        · exact hal_y
        · exact hal_ys _ hb_ys
    · have h_eq : insertDesc x (y :: ys) = y :: insertDesc x ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      intro b hb
      simp at hb
      rcases hb with (rfl | hb')
      · exact hal_y
      · exact IH hax hal_ys b hb'

/-- `insertDesc` preserves `List.Pairwise` under the relation `fun a b => a.2 ≥ b.2`. -/
lemma insertDesc_pairwise {x : α × β} {l : List (α × β)}
    (h : List.Pairwise (fun a b : α × β => a.2 ≥ b.2) l) :
    List.Pairwise (fun a b : α × β => a.2 ≥ b.2) (insertDesc x l) := by
  induction l generalizing x with
  | nil =>
    have h_eq : insertDesc x [] = [x] := by simp [insertDesc]
    rw [h_eq]
    refine List.Pairwise.cons ?_ List.Pairwise.nil
    intro b hb
    simp at hb
  | cons y ys IH =>
    rcases List.pairwise_cons.mp h with ⟨hy_all, hys⟩
    by_cases hcmp : y.2 ≤ x.2
    · have h_eq : insertDesc x (y :: ys) = x :: y :: ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      have hx_ge_y : x.2 ≥ y.2 := hcmp
      have hx_all : ∀ b ∈ (y :: ys), x.2 ≥ b.2 := by
        intro b hb
        rcases List.mem_cons.mp hb with (rfl | hb_ys)
        · exact hx_ge_y
        · have hy_ge_b : y.2 ≥ b.2 := hy_all b hb_ys
          exact le_trans hy_ge_b hx_ge_y
      have h_orig : List.Pairwise (fun a b : α × β => a.2 ≥ b.2) (y :: ys) :=
        List.Pairwise.cons hy_all hys
      exact List.Pairwise.cons hx_all h_orig
    · have h_eq : insertDesc x (y :: ys) = y :: insertDesc x ys := by
        simp [insertDesc, hcmp]
      rw [h_eq]
      have hy_ge_x : y.2 ≥ x.2 := le_of_not_ge hcmp
      have hy_all_insert : ∀ b ∈ insertDesc x ys, y.2 ≥ b.2 :=
        insertDesc_bound hy_ge_x hy_all
      have h_ih : List.Pairwise (fun a b : α × β => a.2 ≥ b.2) (insertDesc x ys) :=
        IH hys
      exact List.Pairwise.cons hy_all_insert h_ih

/-- A `foldl` using `insertDesc` from a pairwise accumulator produces a pairwise list. -/
lemma foldl_insertDesc_pairwise (l acc : List (α × β))
    (h_acc : List.Pairwise (fun a b : α × β => a.2 ≥ b.2) acc) :
    List.Pairwise (fun a b : α × β => a.2 ≥ b.2)
      (l.foldl (fun acc' x => insertDesc x acc') acc) := by
  induction l generalizing acc with
  | nil => exact h_acc
  | cons y ys IH =>
    simp [List.foldl]
    apply IH
    exact insertDesc_pairwise h_acc

/-- Membership in the `foldl` result: a value is in the result iff
it is in the original list or in the accumulator. -/
lemma foldl_insertDesc_mem (l acc : List (α × β)) (x : α × β) :
    x ∈ (l.foldl (fun acc' x' => insertDesc x' acc') acc) ↔ x ∈ l ∨ x ∈ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys IH =>
    simp [List.foldl]
    rw [IH, insertDesc_mem]
    tauto

/-- Folding `insertDesc` over `l` from `[]` produces a list pairwise ordered by `a.2 ≥ b.2`. -/
lemma foldl_insertDesc_pairwise_nil (l : List (α × β)) :
    List.Pairwise (fun a b : α × β => a.2 ≥ b.2)
      (l.foldl (fun acc x => insertDesc x acc) []) := by
  apply foldl_insertDesc_pairwise l []
  exact List.Pairwise.nil

/-- After folding `insertDesc` from `[]`, membership equals membership in the input list. -/
lemma foldl_insertDesc_mem_nil (l : List (α × β)) (x : α × β) :
    x ∈ (l.foldl (fun acc x' => insertDesc x' acc) []) ↔ x ∈ l := by
  rw [foldl_insertDesc_mem l [] x]
  simp

end List

/-! ### `List.insertLexAsc` and `List.sortLexAsc` — insertion sort by second component ascending

`LexAsc` (defined above) compares pairs first by the second component ascending,
then by the first component ascending. `insertLexAsc` inserts a single element
into a `LexAsc`-sorted list, preserving the order. `sortLexAsc` sorts a list
by `LexAsc` using insertion sort.

These are concrete insertion-sort implementations. For a generic sort that works
with any `DecidableRel`, `IsTotal`, `IsTrans` relation, see `List.insertionSort`.
The `LexAsc` relation already has all three instances, so `List.insertionSort LexAsc`
achieves the same result. -/

namespace List

variable {α β : Type _} [LinearOrder α] [LinearOrder β]

/-- Insert `x` into a list that is already sorted by `LexAsc`,
preserving the sorted order. -/
def insertLexAsc (x : α × β) : List (α × β) → List (α × β)
  | [] => [x]
  | h :: t =>
    if LexAsc x h then x :: h :: t
    else h :: insertLexAsc x t

/-- Sort a list of pairs by `LexAsc` using insertion sort. -/
def sortLexAsc : List (α × β) → List (α × β)
  | [] => []
  | h :: t => insertLexAsc h (sortLexAsc t)

/-- Membership lemma for `insertLexAsc`: an element is in the result iff
it is the inserted element or was in the original list. -/
lemma insertLexAsc_mem (x y : α × β) (l : List (α × β)) :
    y ∈ insertLexAsc x l ↔ y = x ∨ y ∈ l := by
  induction l generalizing x y with
  | nil => simp [insertLexAsc]
  | cons h t IH =>
    simp [insertLexAsc]
    split
    · simp
    · simp [IH]
      tauto

/-- `insertLexAsc x l` is a permutation of `x :: l`. -/
lemma insertLexAsc_perm (x : α × β) (l : List (α × β)) :
    List.Perm (insertLexAsc x l) (x :: l) := by
  induction l generalizing x with
  | nil => simp [insertLexAsc]
  | cons h t IH =>
    simp [insertLexAsc]
    split
    · rfl
    · have h_cons : List.Perm (h :: insertLexAsc x t) (h :: x :: t) :=
        List.Perm.cons h (IH x)
      have h_swap : List.Perm (h :: x :: t) (x :: h :: t) :=
        List.Perm.swap x h t
      exact List.Perm.trans h_cons h_swap

/-- If `l` is pairwise ordered by `LexAsc`, then inserting `x` preserves
the pairwise ordering. -/
lemma insertLexAsc_pairwise (x : α × β) (l : List (α × β))
    (h : List.Pairwise LexAsc l) : List.Pairwise LexAsc (insertLexAsc x l) := by
  induction h generalizing x with
  | nil =>
    simp [insertLexAsc, List.Pairwise]
  | @cons a as hall h_pair IH =>
    dsimp [insertLexAsc]
    split
    · rename_i hcond
      have h_all_x : ∀ y ∈ a :: as, LexAsc x y := by
        intro y hy
        rcases List.mem_cons.mp hy with (rfl | hy_as)
        · exact hcond
        · have ha_y : LexAsc a y := hall y hy_as
          exact IsTrans.trans (a := x) (b := a) (c := y) hcond ha_y
      exact List.Pairwise.cons h_all_x (List.Pairwise.cons hall h_pair)
    · rename_i hncond
      have hxa : LexAsc a x := by
        have total_ax := IsTotal.total (α := α × β) (r := LexAsc) (a := x) (b := a)
        rcases total_ax with (hxa' | hax)
        · exact absurd hxa' hncond
        · exact hax
      have h_all_a : ∀ y ∈ insertLexAsc x as, LexAsc a y := by
        intro y hy
        rcases (insertLexAsc_mem x y as).mp hy with (rfl | hy_as)
        · exact hxa
        · exact hall y hy_as
      exact List.Pairwise.cons h_all_a (IH x)

/-- `sortLexAsc l` is a permutation of `l`. -/
lemma sortLexAsc_perm (l : List (α × β)) : List.Perm l (sortLexAsc l) := by
  induction l with
  | nil => simp [sortLexAsc]
  | cons h t IH =>
    simp [sortLexAsc]
    have h1 : List.Perm (insertLexAsc h (sortLexAsc t)) (h :: sortLexAsc t) :=
      insertLexAsc_perm h (sortLexAsc t)
    have h2 : List.Perm (h :: sortLexAsc t) (h :: t) :=
      (List.Perm.cons h IH).symm
    have h_perm : List.Perm (insertLexAsc h (sortLexAsc t)) (h :: t) :=
      List.Perm.trans h1 h2
    exact h_perm.symm

/-- `sortLexAsc l` is pairwise ordered by `LexAsc`. -/
lemma sortLexAsc_pairwise (l : List (α × β)) :
    List.Pairwise LexAsc (sortLexAsc l) := by
  induction l with
  | nil => simp [sortLexAsc, List.Pairwise]
  | cons h t IH =>
    simp [sortLexAsc]
    exact insertLexAsc_pairwise h (sortLexAsc t) IH

end List

