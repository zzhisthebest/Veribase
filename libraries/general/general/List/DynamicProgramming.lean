import Mathlib
import general.List.Argminmax
import general.List.IndexedAccess
import general.List.Predicates

namespace List

/-! # Longest Common Subsequence (LCS) for lists

This module provides `listLCS`, a function that computes a longest common subsequence
of two lists by enumerating all sublists of the first list, filtering those that are
also sublists of the second, and returning the one with maximum length.

This is the simple (exponential) algorithm; suitable for small lists and for
specification/proof purposes. -/

/-- Longest common subsequence of two lists.
Enumerates all sublists of `X`, filters those that are also sublists of `Y`,
and returns the one with maximum length. -/
def listLCS {α : Type u} [DecidableEq α] (X Y : List α) : List α :=
  let candidates := (X.sublists).filter (fun s => s <+ Y)
  maxByLength candidates

/-! ### Membership lemmas for filtered sublists -/

/-- If `s` is in the filtered sublists `(X.sublists).filter (· <+ Y)`, then `s <+ X`. -/
lemma mem_filter_sublists_sub_left {α : Type u} [DecidableEq α] {X Y s : List α}
    (h : s ∈ (X.sublists).filter (fun t => t <+ Y)) : s <+ X := by
  rcases List.mem_filter.mp h with ⟨hs_mem, _⟩
  exact (mem_sublists.mp hs_mem)

/-- If `s` is in the filtered sublists `(X.sublists).filter (· <+ Y)`, then `s <+ Y`. -/
lemma mem_filter_sublists_sub_right {α : Type u} [DecidableEq α] {X Y s : List α}
    (h : s ∈ (X.sublists).filter (fun t => t <+ Y)) : s <+ Y := by
  rcases List.mem_filter.mp h with ⟨_, hs⟩
  simpa using hs

/-- If `s` is a sublist of both `X` and `Y`, then `s` is in the filtered sublists
`(X.sublists).filter (· <+ Y)`. -/
lemma sublist_both_mem_filter_sublists {α : Type u} [DecidableEq α] {X Y s : List α}
    (hsx : s <+ X) (hsy : s <+ Y) : s ∈ (X.sublists).filter (fun t => t <+ Y) := by
  apply List.mem_filter.mpr
  refine ⟨mem_sublists.mpr hsx, ?_⟩
  simpa using hsy

/-! ### Properties of `listLCS` -/

/-- `listLCS X Y` is a sublist of `X`. -/
lemma listLCS_sub_left {α : Type u} [DecidableEq α] (X Y : List α) : listLCS X Y <+ X := by
  unfold listLCS
  apply maxByLength_sublist
  intro s hs
  exact mem_filter_sublists_sub_left hs

/-- `listLCS X Y` is a sublist of `Y`. -/
lemma listLCS_sub_right {α : Type u} [DecidableEq α] (X Y : List α) : listLCS X Y <+ Y := by
  unfold listLCS
  apply maxByLength_sublist
  intro s hs
  exact mem_filter_sublists_sub_right hs

/-- `listLCS X Y` has maximal length among all common subsequences:
for any `s` that is a sublist of both `X` and `Y`, `s.length ≤ (listLCS X Y).length`. -/
lemma listLCS_max_length {α : Type u} [DecidableEq α] (X Y s : List α)
    (hsx : s <+ X) (hsy : s <+ Y) : s.length ≤ (listLCS X Y).length := by
  unfold listLCS
  have hs_mem : s ∈ (X.sublists).filter (fun t => t <+ Y) :=
    sublist_both_mem_filter_sublists hsx hsy
  exact maxByLength_max_length _ s hs_mem

/-! ### Boolean subsequence check

`isSubseqB` is a decidable (boolean) subsequence test. It returns `true` iff all
elements of the first list appear in the second list in order. This is the boolean
counterpart of `Sublist` and is QuickCheck-friendly. -/

/-- Boolean subsequence check (decidable, QuickCheck-friendly).
Returns `true` if `s` is a subsequence of `t`.
General over any type `α` with decidable equality. -/
def isSubseqB {α : Type u} [DecidableEq α] : List α → List α → Bool
| [], _ => true
| _ :: _, [] => false
| a :: as, b :: bs =>
    if a = b then isSubseqB as bs else isSubseqB (a :: as) bs

/-! ### DP-based LCS computation

This section provides `lcsRec`, a dynamic-programming algorithm that computes
a longest common subsequence of two lists. Unlike `listLCS` which enumerates all
sublists (exponential time), `lcsRec` uses the standard O(n*m) DP recursion:
if heads match, include the common character; otherwise, take the longer of
the two sub-problems obtained by skipping either head. -/

/-- Compute the longest common subsequence of two lists using DP recursion.
The algorithm: if heads match, include the common element; otherwise,
take the longer of the two sub-problems obtained by skipping either head. -/
def lcsRec {α : Type u} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
    if x = y then
      x :: lcsRec xs ys
    else
      let sol1 := lcsRec (x :: xs) ys
      let sol2 := lcsRec xs (y :: ys)
      if sol1.length ≥ sol2.length then sol1 else sol2
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by
  · simp_wf; omega
  · simp_wf
  · simp_wf

/-- Compute only the length of the longest common subsequence (without constructing it).
Mirrors the recursion of `lcsRec` but returns `Nat` instead of `List α`.
Useful for proofs where only the length matters, and avoids constructing intermediate lists. -/
def lcsLengthRec {α : Type u} [DecidableEq α] : List α → List α → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x = y then lcsLengthRec xs ys + 1
    else max (lcsLengthRec (x :: xs) ys) (lcsLengthRec xs (y :: ys))
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by
  · simp_wf; omega
  · simp_wf
  · simp_wf

/-- When the heads match, `lcsRec` branches to include the common element. -/
theorem lcsRec_cons_eq {α : Type u} [DecidableEq α] (x : α) (xs ys : List α) :
    lcsRec (x::xs) (x::ys) = x :: lcsRec xs ys := by
  simp [lcsRec]

/-- When the heads differ, `lcsRec` selects the longer of the two sub-problems. -/
theorem lcsRec_cons_ne {α : Type u} [DecidableEq α] {x y : α} (xs ys : List α) (hne : x ≠ y) :
    lcsRec (x::xs) (y::ys) =
      if (lcsRec (x::xs) ys).length ≥ (lcsRec xs (y::ys)).length then
        lcsRec (x::xs) ys
      else
        lcsRec xs (y::ys) := by
  simp [lcsRec, hne]

/-- `lcsRec l₁ l₂` is a sublist of `l₁`. -/
theorem lcsRec_sublist_left {α : Type u} [DecidableEq α] (l₁ l₂ : List α) :
    (lcsRec l₁ l₂).Sublist l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp [lcsRec]
  | cons x xs ih₁ =>
    induction l₂ with
    | nil => simp [lcsRec]
    | cons y ys ih₂ =>
      by_cases hxy : x = y
      · subst hxy
        rw [lcsRec_cons_eq x xs ys]
        exact Sublist.cons₂ x (ih₁ ys)
      · rw [lcsRec_cons_ne xs ys hxy]
        by_cases h_ge : (lcsRec (x::xs) ys).length ≥ (lcsRec xs (y::ys)).length
        · simp [h_ge]
          exact ih₂
        · simp [h_ge]
          exact Sublist.trans (ih₁ (y :: ys)) (Sublist.cons x (Sublist.refl xs))

/-- `lcsRec l₁ l₂` is a sublist of `l₂`. -/
theorem lcsRec_sublist_right {α : Type u} [DecidableEq α] (l₁ l₂ : List α) :
    (lcsRec l₁ l₂).Sublist l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [lcsRec]
  | cons x xs ih₁ =>
    induction l₂ with
    | nil => simp [lcsRec]
    | cons y ys ih₂ =>
      by_cases hxy : x = y
      · subst hxy
        rw [lcsRec_cons_eq x xs ys]
        exact Sublist.cons₂ x (ih₁ ys)
      · rw [lcsRec_cons_ne xs ys hxy]
        by_cases h_ge : (lcsRec (x::xs) ys).length ≥ (lcsRec xs (y::ys)).length
        · simp [h_ge]
          exact Sublist.cons y ih₂
        · simp [h_ge]
          exact ih₁ (y :: ys)

/-! ### Relationship between `lcsRec` and `lcsLengthRec` -/

/-- The length of `lcsRec l₁ l₂` equals `lcsLengthRec l₁ l₂`.
The DP algorithm that constructs the actual subsequence produces a result whose length
matches the length-only counter. -/
theorem lcsRec_length_eq {α : Type u} [DecidableEq α] (l₁ l₂ : List α) :
    (lcsRec l₁ l₂).length = lcsLengthRec l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [lcsRec, lcsLengthRec]
  | cons x xs ih₁ =>
    induction l₂ with
    | nil => simp [lcsRec, lcsLengthRec]
    | cons y ys ih₂ =>
      simp [lcsRec, lcsLengthRec]
      split
      · rename_i h
        subst h
        simp [ih₁ ys]
      · rename_i h
        have h1 := ih₁ (y :: ys)
        have h2 := ih₂
        by_cases hcase : (lcsRec (x :: xs) ys).length ≥ (lcsRec xs (y :: ys)).length
        · rw [if_pos hcase]
          rw [h1, h2] at hcase
          rw [h2, Nat.max_eq_left hcase]
        · rw [if_neg hcase]
          have h_le : (lcsRec xs (y :: ys)).length ≥ (lcsRec (x :: xs) ys).length := by omega
          rw [h1, h2] at h_le
          rw [h1, Nat.max_eq_right h_le]

/-! ### Simplification lemmas for `lcsLengthRec` -/

/-- When the heads match, `lcsLengthRec` simplifies to the tail case plus one. -/

lemma lcsLengthRec_cons_eq {α : Type u} [DecidableEq α] (x : α) (xs ys : List α) :
    lcsLengthRec (x::xs) (x::ys) = lcsLengthRec xs ys + 1 := by
  simp [lcsLengthRec]

/-- When the heads differ, `lcsLengthRec` selects the maximum of the two sub-problems. -/
lemma lcsLengthRec_cons_ne {α : Type u} [DecidableEq α] {x y : α} (h : x ≠ y) (xs ys : List α) :
    lcsLengthRec (x::xs) (y::ys) = max (lcsLengthRec (x::xs) ys) (lcsLengthRec xs (y::ys)) := by
  simp [lcsLengthRec, h]

/-- There exists a common sublist whose length equals `lcsLengthRec xs ys`. -/
lemma lcsLengthRec_exists {α : Type u} [DecidableEq α] (xs ys : List α) :
    ∃ seq, seq <+ xs ∧ seq <+ ys ∧ seq.length = lcsLengthRec xs ys := by
  refine ⟨lcsRec xs ys, lcsRec_sublist_left xs ys, lcsRec_sublist_right xs ys, ?_⟩
  rw [lcsRec_length_eq]

/-- **Optimality for `lcsLengthRec`**: any common sublist `s` of `l₁` and `l₂` has length
at most `lcsLengthRec l₁ l₂`. This is proved directly by induction, avoiding the need to
construct the actual LCS list. -/
theorem lcsLengthRec_upper_bound {α : Type u} [DecidableEq α] (l₁ l₂ s : List α)
    (h₁ : s <+ l₁) (h₂ : s <+ l₂) : s.length ≤ lcsLengthRec l₁ l₂ := by
  induction l₁ generalizing l₂ s with
  | nil =>
    have hs_nil : s = [] := by simpa using h₁
    subst hs_nil
    simp [lcsLengthRec]
  | cons x xs ih₁ =>
    induction l₂ generalizing s with
    | nil =>
      have hs_nil : s = [] := by simpa using h₂
      subst hs_nil
      simp [lcsLengthRec]
    | cons y ys ih₂ =>
      simp [lcsLengthRec]
      cases s with
      | nil => simp
      | cons z_hd z_tl =>
        rcases (sublist_cons_iff.mp h₁) with (hs_xs | ⟨r, h_eq, hs_tl_xs⟩)
        · -- z_hd :: z_tl <+ xs (skip x)
          rcases (sublist_cons_iff.mp h₂) with (hs_ys | ⟨r', h_eq', hs_tl_ys⟩)
          · -- z_hd :: z_tl <+ ys (skip y)
            split
            · rename_i heq
              subst heq
              have hbound := ih₁ ys (z_hd :: z_tl) hs_xs hs_ys
              omega
            · rename_i hne
              have hbound := ih₂ (z_hd :: z_tl) h₁ hs_ys
              apply le_trans hbound
              apply le_max_left
          · -- z_hd = y, z_tl = r', r' <+ ys
            have ⟨hz_hd_eq_y, hz_tl_eq_r'⟩ := List.cons.inj h_eq'
            have s_eq : z_hd :: z_tl = y :: r' := by rw [hz_hd_eq_y, hz_tl_eq_r']
            rw [s_eq]
            have h₁' : y :: r' <+ x :: xs := s_eq ▸ h₁
            have h₂' : y :: r' <+ y :: ys := s_eq ▸ h₂
            have hs_xs' : y :: r' <+ xs := s_eq ▸ hs_xs
            split
            · rename_i heq
              rw [heq] at h₁'
              have hs_tl_xs' : r' <+ xs := (cons_sublist_cons.mp h₁')
              have hbound := ih₁ ys r' hs_tl_xs' hs_tl_ys
              have hlen : (y :: r').length = r'.length + 1 := by simp
              omega
            · rename_i hne
              have hbound := ih₁ (y :: ys) (y :: r') hs_xs' h₂'
              apply le_trans hbound
              apply le_max_right
        · -- z_hd = x, z_tl = r, r <+ xs
          have ⟨hz_hd_eq_x, hz_tl_eq_r⟩ := List.cons.inj h_eq
          have s_eq : z_hd :: z_tl = x :: r := by rw [hz_hd_eq_x, hz_tl_eq_r]
          rw [s_eq]
          have h₁' : x :: r <+ x :: xs := s_eq ▸ h₁
          have h₂' : x :: r <+ y :: ys := s_eq ▸ h₂
          rcases (sublist_cons_iff.mp h₂') with (hs_ys' | ⟨r', h_eq', hs_tl_ys⟩)
          · -- x :: r <+ ys (skip y)
            split
            · rename_i heq
              rw [heq] at h₂'
              rw [heq]
              simp
              have hs_tl_ys' : r <+ ys := (cons_sublist_cons.mp h₂')
              have hbound := ih₁ ys r hs_tl_xs hs_tl_ys'
              omega
            · rename_i hne
              have hbound := ih₂ (x :: r) h₁' hs_ys'
              apply le_trans hbound
              apply le_max_left
          · -- x = y, r = r', r' <+ ys
            have ⟨hx_eq_y, hr_eq_r'⟩ := List.cons.inj h_eq'
            rw [hx_eq_y, hr_eq_r']
            simp
            rw [hr_eq_r'] at hs_tl_xs
            exact ih₁ ys r' hs_tl_xs hs_tl_ys

/-- `lcsRec` produces a common subsequence of maximal length:
for any `z` that is a sublist of both `l₁` and `l₂`,
`z.length ≤ (lcsRec l₁ l₂).length`. -/
theorem lcsRec_maximal {α : Type u} [DecidableEq α] (l₁ l₂ z : List α)
    (h₁ : z.Sublist l₁) (h₂ : z.Sublist l₂) : z.length ≤ (lcsRec l₁ l₂).length := by
  have h_ub := lcsLengthRec_upper_bound l₁ l₂ z h₁ h₂
  have h_len_eq := lcsRec_length_eq l₁ l₂
  rw [← h_len_eq] at h_ub
  exact h_ub

/-- Combined correctness of `lcsRec`: it is a common sublist of both inputs
    and its length is maximal among common sublists. -/
theorem lcsRec_spec {α : Type u} [DecidableEq α] (l₁ l₂ : List α) :
    (lcsRec l₁ l₂).Sublist l₁ ∧ (lcsRec l₁ l₂).Sublist l₂ ∧
      ∀ (z : List α), z.Sublist l₁ → z.Sublist l₂ → z.length ≤ (lcsRec l₁ l₂).length :=
  ⟨lcsRec_sublist_left l₁ l₂, lcsRec_sublist_right l₁ l₂,
    λ z h₁ h₂ => lcsRec_maximal l₁ l₂ z h₁ h₂⟩

/-! ### DP row computation for LCS

`nextLcsRow` computes one row of the DP table for the LCS length problem.
Given the current element `x` of the first list, the whole second list `ys`,
and the previous DP row `prev`, it returns the next row using the standard
LCS DP recurrence: if elements match, diagonal+1; else max(up, left). -/

/-- Compute the next DP row for LCS length.
Given the current element `x` of the first list, the whole second list `ys`,
and the previous DP row `prev`, returns the next row.
Uses the standard LCS DP recurrence. General over any type `α` with decidable equality. -/
def nextLcsRow {α : Type u} [DecidableEq α] (x : α) (ys : List α) (prev : List Nat) : List Nat :=
  let rec go (ys : List α) (j : Nat) (rowSoFar : List Nat) (left : Nat) : List Nat :=
    match ys with
    | [] => rowSoFar.reverse
    | y :: ysTail =>
        let up   := getNat prev (j + 1)  -- dp[i-1][j+1] (default 0 if out of range)
        let diag := getNat prev j        -- dp[i-1][j]   (default 0 if out of range)
        let newVal :=
          if x = y then diag + 1 else Nat.max up left
        go ysTail (j + 1) (newVal :: rowSoFar) newVal
  go ys 0 [0] 0

end List

namespace List

/-! ### Longest Common Subsequence (LCS) -/

/-- Compute the length of the longest common subsequence of two lists.
    Generic over any type `α` with decidable equality. -/
def lcsLength {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  match xs, ys with
  | [], _ => 0
  | _, [] => 0
  | a::as, b::bs =>
    if a = b then
      1 + lcsLength as bs
    else
      max (lcsLength (a::as) bs) (lcsLength as (b::bs))
termination_by xs.length + ys.length
decreasing_by
  · simp_wf; omega
  · simp_wf
  · simp_wf

/-- Correctness of `lcsLength`: the returned value is the maximum length of a common sublist
    of `xs` and `ys`. Specifically, there exists a common sublist of that length,
    and no common sublist can be longer. -/
theorem lcsLength_spec {α : Type} [DecidableEq α] (xs ys : List α) :
    (∃ seq : List α, List.Sublist seq xs ∧ List.Sublist seq ys ∧
      seq.length = lcsLength xs ys) ∧
    (∀ seq : List α, List.Sublist seq xs → List.Sublist seq ys →
      seq.length ≤ lcsLength xs ys) := by
  induction xs generalizing ys with
  | nil =>
    have h_val : lcsLength [] ys = 0 := by simp [lcsLength]
    rw [h_val]
    constructor
    · refine ⟨[], List.nil_sublist _, List.nil_sublist _, rfl⟩
    · intro seq hseq _
      have hnil : seq = [] := (List.sublist_nil.mp hseq)
      subst hnil; rfl
  | cons a as IH_outer =>
    induction ys with
    | nil =>
      have h_val : lcsLength (a :: as) [] = 0 := by simp [lcsLength]
      rw [h_val]
      constructor
      · refine ⟨[], List.nil_sublist _, List.nil_sublist _, rfl⟩
      · intro seq _ hseq
        have hnil : seq = [] := (List.sublist_nil.mp hseq)
        subst hnil; rfl
    | cons b bs IH_inner =>
      by_cases h_eq : a = b
      · subst h_eq
        have h_val : lcsLength (a :: as) (a :: bs) = 1 + lcsLength as bs := by
          simp [lcsLength]
        have h_rec := IH_outer bs
        rcases h_rec with ⟨h_ex, h_opt⟩
        rcases h_ex with ⟨seq, h_seq_as, h_seq_bs, h_seq_len⟩
        constructor
        · refine ⟨a :: seq, ?_, ?_, ?_⟩
          · exact (h_seq_as.cons₂ a)
          · exact (h_seq_bs.cons₂ a)
          · rw [h_val, List.length_cons, h_seq_len]; ring
        · intro seq' h_seq'_xs h_seq'_ys
          rw [h_val]
          rcases sublist_cons_iff.mp h_seq'_xs with (h_sx | ⟨seq_r, h_seq_eq, h_sr⟩)
          · rcases sublist_cons_iff.mp h_seq'_ys with (h_sy | ⟨seq_r', h_seq_eq', h_sr'⟩)
            · have h_le := h_opt seq' h_sx h_sy
              apply Nat.le_trans h_le; omega
            · subst h_seq_eq'
              have h_sr'_as : List.Sublist seq_r' as :=
                sublist_tail_of_cons_sublist h_sx
              have h_le := h_opt seq_r' h_sr'_as h_sr'
              simpa [add_comm] using Nat.succ_le_succ h_le
          · subst h_seq_eq
            rcases sublist_cons_iff.mp h_seq'_ys with (h_sy | ⟨seq_r', h_seq_eq', h_sr'⟩)
            · have h_sr_bs : List.Sublist seq_r bs :=
                sublist_tail_of_cons_sublist h_sy
              have h_le := h_opt seq_r h_sr h_sr_bs
              simpa [add_comm] using Nat.succ_le_succ h_le
            · injection h_seq_eq' with _ h_eq_r
              subst h_eq_r
              have h_le := h_opt seq_r h_sr h_sr'
              simpa [add_comm] using Nat.succ_le_succ h_le
      · have h_val : lcsLength (a :: as) (b :: bs) =
            max (lcsLength (a :: as) bs) (lcsLength as (b :: bs)) := by
          simp [lcsLength, h_eq]
        have h_rec1 := IH_inner
        have h_rec2 := IH_outer (b :: bs)
        rcases h_rec1 with ⟨h_ex1, h_opt1⟩
        rcases h_rec2 with ⟨h_ex2, h_opt2⟩
        set L1 := lcsLength (a :: as) bs
        set L2 := lcsLength as (b :: bs)
        rcases h_ex1 with ⟨seq1, h_s1x, h_s1y, h_len1⟩
        rcases h_ex2 with ⟨seq2, h_s2x, h_s2y, h_len2⟩
        have h_max : lcsLength (a :: as) (b :: bs) = max L1 L2 := h_val
        rw [h_max]
        constructor
        · by_cases h_le12 : L1 ≤ L2
          · refine ⟨seq2, ?_, ?_, ?_⟩
            · exact h_s2x.trans (List.sublist_cons_self a as)
            · exact h_s2y
            · rw [h_len2]; simp [h_le12]
          · refine ⟨seq1, ?_, ?_, ?_⟩
            · exact h_s1x
            · exact h_s1y.cons b
            · rw [h_len1]
              have h_gt : L2 ≤ L1 := by omega
              simp [h_gt]
        · intro seq' h_seq'_xs h_seq'_ys
          rcases sublist_cons_iff.mp h_seq'_xs with (h_sx | ⟨seq_r1, h_seq_eq1, h_sr1⟩)
          · rcases sublist_cons_iff.mp h_seq'_ys with (h_sy | ⟨seq_r2, h_seq_eq2, h_sr2⟩)
            · have h_le := h_opt1 seq' (h_sx.trans (List.sublist_cons_self a as)) h_sy
              have hL1le : L1 ≤ max L1 L2 := by simp
              apply Nat.le_trans h_le; omega
            · subst h_seq_eq2
              have h_temp : List.Sublist (b :: seq_r2) (b :: bs) := (h_sr2.cons₂ b)
              have h_le := h_opt2 (b :: seq_r2) h_sx h_temp
              have hL2le : L2 ≤ max L1 L2 := by simp
              apply Nat.le_trans h_le; omega
          · subst h_seq_eq1
            rcases sublist_cons_iff.mp h_seq'_ys with (h_sy | ⟨seq_r2, h_seq_eq2, h_sr2⟩)
            · have h_le := h_opt1 (a :: seq_r1) (h_sr1.cons₂ a) h_sy
              have hL1le : L1 ≤ max L1 L2 := by simp
              apply Nat.le_trans h_le; omega
            · have h_eq_ab : a = b := by
                injection h_seq_eq2
              exact absurd h_eq_ab h_eq

end List



namespace List

/-! ### Edit distance -/

/--
Checks if `short` can become `longer` by inserting exactly one element.
Returns `true` iff there exists an index in `longer` such that deleting that
element yields `short`.
-/
def oneEditInsert {α : Type _} [DecidableEq α] (short longer : List α) : Bool :=
  match short, longer with
  | [], _::_ => true
  | c₁ :: r₁, c₂ :: r₂ =>
      if c₁ = c₂ then
        oneEditInsert r₁ r₂
      else
        r₁ = r₂
  | _, [] => false

/--
Checks if `l₁` and `l₂` differ by exactly one element replacement.
Only applicable when the lists have the same length.
-/
def oneEditReplace {α : Type _} [DecidableEq α] (l₁ l₂ : List α) : Bool :=
  let rec go (xs ys : List α) (found : Bool) : Bool :=
    match xs, ys with
    | [], [] => found
    | x :: xs', y :: ys' =>
        if x = y then
          go xs' ys' found
        else
          if found then false
          else go xs' ys' true
    | _, _ => false
  go l₁ l₂ false

/--
`true` iff `l₁` and `l₂` are one edit distance apart
(insert/delete/replace exactly one element). General over any `α` with decidable equality.
-/
def isOneEditDistance {α : Type _} [DecidableEq α] (l₁ l₂ : List α) : Bool :=
  if l₁.length + 1 = l₂.length then
    oneEditInsert l₁ l₂
  else if l₂.length + 1 = l₁.length then
    oneEditInsert l₂ l₁
  else if l₁.length = l₂.length then
    oneEditReplace l₁ l₂
  else
    false

end List

namespace List

/-- Maximum sum of non-adjacent elements in a list.
Implements the classic "House Robber" dynamic programming algorithm:
given a list of natural numbers, compute the maximum sum of a subset
where no two selected elements are adjacent in the list.
Returns `0` for the empty list and `x` for `[x]`. -/
def maxNonAdjacentSum : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: zs => Nat.max (x + maxNonAdjacentSum zs) (maxNonAdjacentSum (y :: zs))

/-- Rewrite rule for `maxNonAdjacentSum` on a list with at least two elements:
the recursive case that chooses between taking the first element plus the tail's
non-adjacent sum, and skipping the first element. -/
lemma maxNonAdjacentSum_cons_cons (x y : Nat) (zs : List Nat) :
    maxNonAdjacentSum (x :: y :: zs) = Nat.max (x + maxNonAdjacentSum zs) (maxNonAdjacentSum (y :: zs)) := rfl

end List
