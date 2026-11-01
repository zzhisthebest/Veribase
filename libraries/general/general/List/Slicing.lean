import Mathlib
import general.Finite.Core
import general.List.Predicates

namespace List

/-! # Prefix and suffix maximum operations

This module defines operations for computing the maximum value in
prefixes and suffixes of a list, with respect to an index.

These are used in problems that require knowing the maximum value
to the left or right of a position (e.g., trapping rain water).
-/

/-- The maximum value in the prefix of `xs` before index `i` (exclusive).
That is, `max { xs[0], xs[1], ..., xs[i-1] }`, returning `⊥` when `i = 0`. -/
def prefixMax [SemilatticeSup α] [OrderBot α] (xs : List α) (i : Nat) : α :=
  (xs.take i).foldl (· ⊔ ·) ⊥

/-- The maximum value in the suffix of `xs` after index `i` (exclusive).
That is, `max { xs[i+1], xs[i+2], ... }`, returning `⊥` when the suffix is empty. -/
def suffixMax [SemilatticeSup α] [OrderBot α] (xs : List α) (i : Nat) : α :=
  (xs.drop (i + 1)).foldl (· ⊔ ·) ⊥

lemma prefixMax_zero [SemilatticeSup α] [OrderBot α] (xs : List α) :
    prefixMax xs 0 = (⊥ : α) := by
  simp [prefixMax]

lemma prefixMax_nil [SemilatticeSup α] [OrderBot α] (n : Nat) :
    prefixMax ([] : List α) n = (⊥ : α) := by
  simp [prefixMax]

lemma prefixMax_eq_of_length_le [SemilatticeSup α] [OrderBot α] (l : List α) (n : Nat)
    (h : l.length ≤ n) : prefixMax l n = prefixMax l l.length := by
  have h_take : l.take n = l := List.take_of_length_le h
  simp [prefixMax, h_take]

lemma suffixMax_nil [SemilatticeSup α] [OrderBot α] (i : Nat) :
    suffixMax ([] : List α) i = (⊥ : α) := by
  simp [suffixMax]

/-- Length of the longest common prefix of two lists.
The prefix stops at the first position where elements differ (or one list ends). -/
def commonPrefixLength {α : Type} [DecidableEq α] (l1 l2 : List α) : Nat :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | h1 :: t1, h2 :: t2 => if h1 = h2 then 1 + commonPrefixLength t1 t2 else 0


lemma commonPrefixLength_nil_left {α : Type} [DecidableEq α] (l : List α) :
    commonPrefixLength ([] : List α) l = 0 := by
  simp [commonPrefixLength]


lemma commonPrefixLength_nil_right {α : Type} [DecidableEq α] (l : List α) :
    commonPrefixLength l ([] : List α) = 0 := by
  cases l <;> simp [commonPrefixLength]

/-! ### `take_eq_of_prefix` / `prefix_of_take_eq` — equivalence between `IsPrefix` and `take`

These two lemmas bridge the `IsPrefix` relation with the `take` operation, providing
single-direction access to the equivalence `prefix_iff_eq_take` from mathlib.
They are frequently used when translating between prefix-based and take-based proofs.
-/

/-- If `p` is a prefix of `l`, then taking `p.length` elements from `l` gives `p`.
This is the forward direction of `List.prefix_iff_eq_take`. -/
lemma take_eq_of_prefix {p l : List α} (h : p <+: l) : l.take p.length = p := by
  rcases h with ⟨t, ht⟩
  rw [← ht, List.take_left]

/-- If taking `p.length` elements from `l` gives `p`, then `p` is a prefix of `l`.
This is the reverse direction of `List.prefix_iff_eq_take`. -/
lemma prefix_of_take_eq {l p : List α} (h : l.take p.length = p) : p <+: l := by
  have h_append : p ++ l.drop p.length = l := by
    calc
      p ++ l.drop p.length = l.take p.length ++ l.drop p.length := by rw [h]
      _ = l := by rw [List.take_append_drop]
  exact ⟨l.drop p.length, h_append⟩

/-! ### `prefixOfVal` — length of the initial prefix where all elements equal a given value -/

/-- The length of the prefix consisting entirely of `val`.
Returns the number of leading elements in `l` that are all equal to `val`. -/
def prefixOfVal {α : Type} [DecidableEq α] (l : List α) (val : α) : Nat :=
  match l with
  | h :: t => if h = val then 1 + prefixOfVal t val else 0
  | [] => 0

/-- `prefixOfVal` is bounded by the list length. -/
lemma prefixOfVal_le_length {α : Type} [DecidableEq α] (l : List α) (val : α) :
    prefixOfVal l val ≤ l.length := by
  induction l generalizing val with
  | nil => simp [prefixOfVal]
  | cons h t ih =>
    by_cases hh : h = val
    · rw [hh]
      simp [prefixOfVal]
      have h := ih val
      omega
    · have hpref : prefixOfVal (h :: t) val = 0 := by simp [prefixOfVal, hh]
      rw [hpref]; exact Nat.zero_le _

/-- Every element within the prefix returned by `prefixOfVal` is indeed `val`. -/
lemma prefixOfVal_spec {α : Type} [DecidableEq α] (l : List α) (val : α) :
    ∀ i, i < prefixOfVal l val → l[i]? = some val := by
  induction l generalizing val with
  | nil => intro i hi; simp [prefixOfVal] at hi
  | cons h t ih =>
    intro i hi
    by_cases hh : h = val
    · rw [hh] at hi ⊢
      simp [prefixOfVal] at hi
      cases i with
      | zero => simp
      | succ i' =>
        have hi' : i' < prefixOfVal t val := by omega
        exact ih val i' hi'
    · simp [prefixOfVal, hh] at hi

/-- If all elements up to index `len` are `val`, then `len ≤ prefixOfVal l val`.
This is the converse direction to `prefixOfVal_spec`. -/
lemma prefixOfVal_ge_of_all_val {α : Type} [DecidableEq α] (l : List α) (val : α) (len : Nat)
    (h : ∀ k, k < len → l[k]? = some val) : len ≤ prefixOfVal l val := by
  revert h
  induction l generalizing val len with
  | nil =>
    intro h
    by_cases hlen0 : len = 0
    · subst hlen0; simp [prefixOfVal]
    · have hpos : 0 < len := Nat.pos_of_ne_zero hlen0
      have h0 := h 0 hpos
      simp at h0
  | cons hd tl ih =>
    intro h
    by_cases hlen0 : len = 0
    · subst hlen0; simp [prefixOfVal]
    · have hpos : 0 < len := Nat.pos_of_ne_zero hlen0
      have h0 := h 0 hpos
      simp at h0
      rw [h0]
      simp [prefixOfVal]
      have h_rest : ∀ k, k < len - 1 → tl[k]? = some val := by
        intro k hk
        have hk' : k + 1 < len := by omega
        have hk1 := h (k + 1) hk'
        simpa using hk1
      have ih' := ih val (len - 1) h_rest
      omega

/-! ### `commonPrefix` — longest common prefix of two lists

`commonPrefix` returns the longest common prefix of two lists as a list of elements.
This is the list-valued companion to `commonPrefixLength` which returns only the length.
-/


/-- Find the longest common prefix of two lists (returns the list itself).
Contrast with `commonPrefixLength` which returns only the length. -/
def commonPrefix {α : Type u} [DecidableEq α] (a b : List α) : List α :=
  match a, b with
  | [], _ => []
  | _, [] => []
  | ha :: ta, hb :: tb => if ha = hb then ha :: commonPrefix ta tb else []

lemma commonPrefix_nil_left {α : Type u} [DecidableEq α] (b : List α) : commonPrefix [] b = [] := by
  simp [commonPrefix]

lemma commonPrefix_nil_right {α : Type u} [DecidableEq α] (a : List α) : commonPrefix a [] = [] := by
  cases a <;> simp [commonPrefix]

lemma commonPrefix_prefix_left {α : Type u} [DecidableEq α] (a b : List α) :
    a.take (commonPrefix a b).length = commonPrefix a b := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys => by_cases h : x = y <;> simp [commonPrefix, h, ih]

lemma commonPrefix_prefix_right {α : Type u} [DecidableEq α] (a b : List α) :
    b.take (commonPrefix a b).length = commonPrefix a b := by
  induction a generalizing b with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefix]
    | cons y ys => by_cases h : x = y <;> simp [commonPrefix, h, ih]

lemma commonPrefix_longest {α : Type u} [DecidableEq α] (a b p : List α)
    (hpa : a.take p.length = p) (hpb : b.take p.length = p) :
    p.length ≤ (commonPrefix a b).length := by
  induction p generalizing a b with
  | nil => simp
  | cons h t ih =>
    have h_len : (h :: t).length = t.length + 1 := by simp
    rw [h_len] at hpa hpb
    cases a with
    | nil => simp at hpa
    | cons ha ta =>
      cases b with
      | nil => simp at hpb
      | cons hb tb =>
        have h_take_succ_a : (ha :: ta).take (t.length + 1) = ha :: ta.take t.length := by
          simp
        rw [h_take_succ_a] at hpa
        have h_take_succ_b : (hb :: tb).take (t.length + 1) = hb :: tb.take t.length := by
          simp
        rw [h_take_succ_b] at hpb
        have hha : ha = h := by
          injection hpa
        have hhb : hb = h := by
          injection hpb
        have hta_prefix : ta.take t.length = t := by
          injection hpa
        have htb_prefix : tb.take t.length = t := by
          injection hpb
        have h_heads_eq : ha = hb := by rw [hha, hhb]
        simp [commonPrefix, h_heads_eq]
        exact ih ta tb hta_prefix htb_prefix

/-- `commonPrefix a b` is a prefix of `a`. This is the IsPrefix-formulation of
`commonPrefix_prefix_left` which uses the `take` formulation instead. -/
lemma commonPrefix_isPrefix_left {α : Type u} [DecidableEq α] (a b : List α) :
    commonPrefix a b <+: a := by
  rw [← commonPrefix_prefix_left a b]
  exact List.take_prefix _ _

/-- `commonPrefix a b` is a prefix of `b`. IsPrefix-formulation of `commonPrefix_prefix_right`. -/
lemma commonPrefix_isPrefix_right {α : Type u} [DecidableEq α] (a b : List α) :
    commonPrefix a b <+: b := by
  rw [← commonPrefix_prefix_right a b]
  exact List.take_prefix _ _

/-- Maximality: if `p` is a prefix of both `a` and `b`, then `p` is a prefix of
`commonPrefix a b`. This is the IsPrefix-formulation of `commonPrefix_longest`. -/
lemma commonPrefix_isPrefix_maximal {α : Type u} [DecidableEq α] (p a b : List α)
    (h₁ : p <+: a) (h₂ : p <+: b) : p <+: commonPrefix a b := by
  induction' p with cp csp ih generalizing a b
  · exact ⟨commonPrefix a b, by simp⟩
  · rcases h₁ with ⟨t₁, ht₁⟩
    rcases h₂ with ⟨t₂, ht₂⟩
    have h_cons1 : cp :: (csp ++ t₁) = a := ht₁
    have h_cons2 : cp :: (csp ++ t₂) = b := ht₂
    cases a with
    | nil => simp at ht₁
    | cons ha ta =>
      cases b with
      | nil => simp at ht₂
      | cons hb tb =>
        have hdecomp1 := List.cons_eq_cons.mp h_cons1
        have hdecomp2 := List.cons_eq_cons.mp h_cons2
        rcases hdecomp1 with ⟨hc1, htail1⟩
        rcases hdecomp2 with ⟨hc2, htail2⟩
        subst hc1; subst hc2
        subst htail1; subst htail2
        have h_csp_a : csp <+: (csp ++ t₁) := ⟨t₁, rfl⟩
        have h_csp_b : csp <+: (csp ++ t₂) := ⟨t₂, rfl⟩
        have ih_res : csp <+: commonPrefix (csp ++ t₁) (csp ++ t₂) :=
          ih (csp ++ t₁) (csp ++ t₂) h_csp_a h_csp_b
        rcases ih_res with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        calc
          (cp :: csp) ++ t = cp :: (csp ++ t) := by simp
          _ = cp :: commonPrefix (csp ++ t₁) (csp ++ t₂) := by rw [ht]
          _ = commonPrefix (cp :: (csp ++ t₁)) (cp :: (csp ++ t₂)) := by simp [commonPrefix]

/-- The length of `commonPrefix a b` is bounded by the length of `a`. -/
lemma commonPrefix_length_le_left {α : Type u} [DecidableEq α] (a b : List α) :
    (commonPrefix a b).length ≤ a.length :=
  (commonPrefix_isPrefix_left a b).length_le

/-- The length of `commonPrefix a b` is bounded by the length of `b`. -/
lemma commonPrefix_length_le_right {α : Type u} [DecidableEq α] (a b : List α) :
    (commonPrefix a b).length ≤ b.length :=
  (commonPrefix_isPrefix_right a b).length_le

/-! ### `commonPrefixFold` — folding `commonPrefix` over a list of lists -/

/-- Fold `commonPrefix` over a list of lists, starting from an initial accumulator.
This computes the common prefix of all lists in the input. -/
def commonPrefixFold {α : Type u} [DecidableEq α] (acc : List α) (ss : List (List α)) : List α :=
  ss.foldl commonPrefix acc

lemma commonPrefixFold_prefix {α : Type u} [DecidableEq α] (acc : List α) (ss : List (List α)) :
    (acc.take (commonPrefixFold acc ss).length = commonPrefixFold acc ss) ∧
    (∀ s ∈ ss, s.take (commonPrefixFold acc ss).length = commonPrefixFold acc ss) := by
  induction ss generalizing acc with
  | nil =>
    simp [commonPrefixFold]
  | cons s ts ih =>
    have h_fold_eq : commonPrefixFold acc (s :: ts) = commonPrefixFold (commonPrefix acc s) ts := by
      simp [commonPrefixFold]
    rw [h_fold_eq]
    let mid := commonPrefix acc s
    have h_mid_prefix_left : acc.take mid.length = mid := commonPrefix_prefix_left acc s
    have h_mid_prefix_right : s.take mid.length = mid := commonPrefix_prefix_right acc s
    have h_ih := ih mid
    rcases h_ih with ⟨hacc, hmem⟩
    let res := commonPrefixFold mid ts
    have h_len_le : res.length ≤ mid.length := by
      have hlen_eq : res.length = (mid.take res.length).length := by rw [hacc]
      rw [hlen_eq, List.length_take]
      omega
    have h_acc_res : acc.take res.length = res := by
      calc
        acc.take res.length = (acc.take mid.length).take res.length := by
          rw [List.take_take, Nat.min_eq_left h_len_le]
        _ = mid.take res.length := by rw [h_mid_prefix_left]
        _ = res := hacc
    have h_s_res : s.take res.length = res := by
      calc
        s.take res.length = (s.take mid.length).take res.length := by
          rw [List.take_take, Nat.min_eq_left h_len_le]
        _ = mid.take res.length := by rw [h_mid_prefix_right]
        _ = res := hacc
    refine ⟨h_acc_res, ?_⟩
    intro s' hs'
    rcases List.mem_cons.mp hs' with (rfl | hs'_in_ts)
    · exact h_s_res
    · exact hmem s' hs'_in_ts

lemma commonPrefixFold_longest {α : Type u} [DecidableEq α] (acc : List α) (ss : List (List α)) (p : List α)
    (h_acc_prefix : acc.take p.length = p) (h_ss_prefix : ∀ s ∈ ss, s.take p.length = p) :
    p.length ≤ (commonPrefixFold acc ss).length := by
  induction ss generalizing acc with
  | nil =>
    simp [commonPrefixFold]
    have h_len_le : p.length ≤ acc.length := by
      have := calc
        p.length = (acc.take p.length).length := by rw [h_acc_prefix]
        _ = p.length ⊓ acc.length := List.length_take p.length acc
      omega
    exact h_len_le
  | cons s ts ih =>
    have h_fold_eq : commonPrefixFold acc (s :: ts) = commonPrefixFold (commonPrefix acc s) ts := by
      simp [commonPrefixFold]
    rw [h_fold_eq]
    let mid := commonPrefix acc s
    have h_s_prefix : s.take p.length = p := h_ss_prefix s (by simp)
    have h_mid_longest : p.length ≤ mid.length :=
      commonPrefix_longest acc s p h_acc_prefix h_s_prefix
    have h_mid_prefix_left : acc.take mid.length = mid := commonPrefix_prefix_left acc s
    have h_mid_acc_prefix : mid.take p.length = p := by
      calc
        mid.take p.length = (acc.take mid.length).take p.length := by rw [h_mid_prefix_left]
        _ = acc.take (p.length ⊓ mid.length) := by rw [List.take_take]
        _ = acc.take p.length := by rw [Nat.min_eq_left h_mid_longest]
        _ = p := h_acc_prefix
    have h_ts_prefix : ∀ t ∈ ts, t.take p.length = p := by
      intro t ht
      apply h_ss_prefix t
      exact List.mem_cons_of_mem s ht
    exact ih mid h_mid_acc_prefix h_ts_prefix

/-- Folding `commonPrefix` over a list preserves prefix of the initial accumulator:
`commonPrefixFold acc ss` is a prefix of `acc`. This is the IsPrefix-formulation
of the first component of `commonPrefixFold_prefix`. -/
lemma commonPrefixFold_isPrefix_init {α : Type u} [DecidableEq α] (acc : List α)
    (ss : List (List α)) : commonPrefixFold acc ss <+: acc := by
  induction' ss with s ss' ih generalizing acc
  · exact ⟨[], by simp [commonPrefixFold]⟩
  · simp [commonPrefixFold, List.foldl]
    have h_prefix_fold : commonPrefixFold (commonPrefix acc s) ss' <+: commonPrefix acc s := ih (commonPrefix acc s)
    have h_prefix_cp : commonPrefix acc s <+: acc := commonPrefix_isPrefix_left acc s
    exact IsPrefix.trans h_prefix_fold h_prefix_cp

/-- Folding `commonPrefix` over a list gives a result that is a prefix of
each element in the list. This is the IsPrefix-formulation of the second
component of `commonPrefixFold_prefix`. -/
lemma commonPrefixFold_isPrefix_mem {α : Type u} [DecidableEq α] (acc : List α)
    (ss : List (List α)) (s : List α) (hs : s ∈ ss) : commonPrefixFold acc ss <+: s := by
  induction' ss with t ts ih generalizing acc
  · simp at hs
  · simp at hs
    rcases hs with (rfl | hs')
    · simp [commonPrefixFold, List.foldl]
      have h_fold_prefix : commonPrefixFold (commonPrefix acc s) ts <+: commonPrefix acc s :=
        commonPrefixFold_isPrefix_init (commonPrefix acc s) ts
      have h_cp_right : commonPrefix acc s <+: s := commonPrefix_isPrefix_right acc s
      exact IsPrefix.trans h_fold_prefix h_cp_right
    · simp [commonPrefixFold, List.foldl]
      exact ih (commonPrefix acc t) hs'

/-- Maximality of `commonPrefixFold`: if `p` is a prefix of `acc` and of every element
in `ss`, then `p` is a prefix of `commonPrefixFold acc ss`. This is the IsPrefix-formulation
of `commonPrefixFold_longest`. -/
lemma commonPrefixFold_isPrefix_maximal {α : Type u} [DecidableEq α] (p acc : List α)
    (ss : List (List α)) (hp_acc : p <+: acc) (hp_all : ∀ s ∈ ss, p <+: s) :
    p <+: commonPrefixFold acc ss := by
  induction' ss with s ss' ih generalizing acc
  · simp [commonPrefixFold]; exact hp_acc
  · have hp_s : p <+: s := hp_all s (by simp)
    have hp_cp : p <+: commonPrefix acc s :=
      commonPrefix_isPrefix_maximal p acc s hp_acc hp_s
    have hp_all' : ∀ s' ∈ ss', p <+: s' := by
      intro s' hs'
      apply hp_all s'
      simp [hs']
    simp [commonPrefixFold, List.foldl]
    exact ih (commonPrefix acc s) hp_cp hp_all'

/-! ### Generic foldl lemmas preserving `IsPrefix`

These lemmas generalize the `commonPrefixFold_*` results above. Instead of being
specialized to `commonPrefix`, they work with any folding function `f` and projection
`g` that satisfy appropriate prefix-preservation hypotheses. This enables reuse
across different LCP-like and other prefix-fold algorithms.
-/

/-- If `f` always returns a prefix of its first argument (`f a b <+: a`), then
folding `f ∘ g` over `bs` starting from `acc` returns a prefix of `acc`.
This generalizes `commonPrefixFold_isPrefix_init` from `commonPrefix` to any
prefix-preserving binary operation. -/
lemma foldl_prefix_acc {α β : Type u} (f : List α → List α → List α) (g : β → List α)
    (hf : ∀ a b, f a b <+: a) (acc : List α) (bs : List β) :
    (List.foldl (λ a b => f a (g b)) acc bs) <+: acc := by
  induction bs generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons b bs ih =>
    simp [List.foldl]
    have h1 := ih (f acc (g b))
    have h2 := hf acc (g b)
    exact IsPrefix.trans h1 h2

/-- If `f` returns a prefix of both its arguments (`f a b <+: a` and `f a b <+: b`),
then folding `f ∘ g` over `bs` from `acc` gives a result that is a prefix of `g b`
for each `b ∈ bs`.
This generalizes `commonPrefixFold_isPrefix_mem` from `commonPrefix` to any
prefix-preserving binary operation. -/
lemma foldl_prefix_each {α β : Type u} (f : List α → List α → List α) (g : β → List α)
    (hf_left : ∀ a b, f a b <+: a) (hf_right : ∀ a b, f a b <+: b)
    (acc : List α) (bs : List β) (b : β) (hb : b ∈ bs) :
    (List.foldl (λ a b' => f a (g b')) acc bs) <+: g b := by
  induction bs generalizing acc with
  | nil => exact absurd hb (by simp)
  | cons b' bs ih =>
    simp only [List.foldl]
    rcases (List.mem_cons.mp hb) with (rfl | hb')
    · have h1 := foldl_prefix_acc f g hf_left (f acc (g b)) bs
      have h2 := hf_right acc (g b)
      exact IsPrefix.trans h1 h2
    · exact ih (f acc (g b')) hb'

/-- Maximality of `foldl` for common prefixes: if `p` is a prefix of both `acc`
and every `g b` for `b ∈ bs`, and `f` preserves being-a-common-prefix (i.e., if `p`
is a prefix of both `a` and `b`, then `p` is a prefix of `f a b`), then the length
of `p` is bounded by the length of the fold result.
This generalizes `commonPrefixFold_longest`. -/
lemma foldl_maximal {α β : Type u} (f : List α → List α → List α) (g : β → List α)
    (hf : ∀ a b p, p <+: a → p <+: b → p <+: f a b)
    (acc : List α) (bs : List β) (p : List α)
    (hp_acc : p <+: acc) (hp_bs : ∀ b ∈ bs, p <+: g b) :
    p.length ≤ (List.foldl (λ a b => f a (g b)) acc bs).length := by
  induction bs generalizing acc with
  | nil => exact hp_acc.length_le
  | cons b bs ih =>
    simp [List.foldl]
    have hp_b : p <+: g b := hp_bs b (by simp)
    have hp_lcp : p <+: f acc (g b) := hf acc (g b) p hp_acc hp_b
    have hp_bs' : ∀ b' ∈ bs, p <+: g b' := by
      intro b' hb'
      exact hp_bs b' (by simp [hb'])
    exact ih (f acc (g b)) hp_lcp hp_bs'

/-! ### `commonPrefixOfList` — common prefix of a list via a projection -/

/-- Compute the longest common prefix of all `f x` for `x` in a list.
For an empty list, returns `[]`. For a non-empty list `first :: rest`,
uses `commonPrefixFold` initialized with `f first` over the mapped `rest`.
This generalizes `commonPrefix` to an arbitrary number of lists via a projection
function `f`. -/
def commonPrefixOfList {α : Type u} [DecidableEq α] (f : β → List α) : List β → List α
  | [] => []
  | first :: rest => (rest.map f).foldl commonPrefix (f first)

/-- Maximality of `commonPrefixOfList`: if `p` is a prefix of `f x` for every `x` in
`a :: rest`, then `p` is a prefix of `commonPrefixOfList f (a :: rest)`. -/
lemma commonPrefixOfList_maximal {α : Type u} [DecidableEq α] (f : β → List α)
    (a : β) (rest : List β) (p : List α)
    (hp_all : ∀ x ∈ (a :: rest), p <+: f x) : p <+: commonPrefixOfList f (a :: rest) := by
  unfold commonPrefixOfList
  have hp_first : p <+: f a := hp_all a (by simp)
  have hp_rest : ∀ y ∈ rest.map f, p <+: y := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hp_all x (by simp [hx])
  exact commonPrefixFold_isPrefix_maximal p (f a) (rest.map f) hp_first hp_rest

end List

namespace List

/-! ### Common prefix -/

/-- Drop the longest common prefix of two lists.
    Returns the remaining suffixes `(s₁', s₂')` such that
    `l₁ = p ++ s₁'` and `l₂ = p ++ s₂'` where `p` is the longest common prefix. -/
def dropCommonPrefix {α : Type u} [DecidableEq α] : List α → List α → List α × List α
  | [], l => ([], l)
  | s, [] => (s, [])
  | (h₁::t₁), (h₂::t₂) =>
      if h₁ = h₂ then
        dropCommonPrefix t₁ t₂
      else
        ((h₁::t₁), (h₂::t₂))


lemma dropCommonPrefix_nil_left {α : Type u} [DecidableEq α] (l : List α) :
    dropCommonPrefix [] l = ([], l) := by
  simp [dropCommonPrefix]

/-- Length of the longest common prefix of two lists.
`lcpLength l₁ l₂` returns the number of initial elements where `l₁` and `l₂` agree. -/
def lcpLength {α : Type u} [DecidableEq α] (l₁ l₂ : List α) : Nat :=
  let rec go (l₁ l₂ : List α) (n : Nat) : Nat :=
    match l₁, l₂ with
    | c₁ :: t₁, c₂ :: t₂ =>
        if c₁ = c₂ then go t₁ t₂ (n + 1) else n
    | _, _ => n
  go l₁ l₂ 0


lemma lcpLength_nil_left {α : Type u} [DecidableEq α] (l : List α) : lcpLength [] l = 0 := by
  unfold lcpLength; rfl


lemma lcpLength_nil_right {α : Type u} [DecidableEq α] (l : List α) : lcpLength l [] = 0 := by
  induction l with
  | nil => unfold lcpLength; rfl
  | cons _ _ => unfold lcpLength; rfl

/-- The length of the longest common prefix of a list with itself is the list's length. -/

lemma lcpLength_self {α : Type u} [DecidableEq α] (l : List α) : lcpLength l l = l.length := by
  have aux (xs : List α) (n : Nat) : lcpLength.go xs xs n = n + xs.length := by
    induction xs generalizing n with
    | nil => simp [lcpLength.go]
    | cons x xs ih => simp [lcpLength.go, ih]; omega
  simpa [lcpLength] using aux l 0

/-! ### Simple LCP (direct structural recursion) -/

/-- Compute the length of the longest common prefix of two lists by direct structural recursion.
Unlike `lcpLength`, this version avoids an explicit accumulator, making it easier to reason about
by induction on the list structure. -/
def listLCP {α : Type u} [DecidableEq α] : List α → List α → Nat
  | c₁::cs₁, c₂::cs₂ => if c₁ = c₂ then 1 + listLCP cs₁ cs₂ else 0
  | _, _ => 0

/-- `listLCP` is symmetric: the longest common prefix of `xs` and `ys` equals that of `ys` and `xs`. -/
lemma listLCP_symm {α : Type u} [DecidableEq α] (xs ys : List α) : listLCP xs ys = listLCP ys xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp [listLCP]
      split
      · next h_eq =>
        rw [h_eq]
        simp [ih]
      · next h_ne =>
        have h_ne' : y ≠ x := by
          intro h; apply h_ne; exact h.symm
        simp [h_ne']

/-- The LCP of a list with itself equals the list's length. -/

lemma listLCP_eq_self {α : Type u} [DecidableEq α] (xs : List α) : listLCP xs xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [listLCP, ih]
    omega

/-- The LCP of two lists is bounded by the length of the first list. -/
lemma listLCP_le_length_left {α : Type u} [DecidableEq α] (xs ys : List α) : listLCP xs ys ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp [listLCP]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listLCP]
    | cons y ys =>
      simp [listLCP]
      split
      · next h_eq =>
        have this : listLCP xs ys ≤ xs.length := ih ys
        omega
      · simp

/-- The LCP of two lists is bounded by the length of the second list. -/
lemma listLCP_le_length_right {α : Type u} [DecidableEq α] (xs ys : List α) : listLCP xs ys ≤ ys.length := by
  rw [listLCP_symm]
  exact listLCP_le_length_left ys xs

/-- The prefix of `xs` of length `listLCP xs ys` equals the prefix of `ys` of that same length. -/
lemma listLCP_take_eq {α : Type u} [DecidableEq α] (xs ys : List α) :
    xs.take (listLCP xs ys) = ys.take (listLCP xs ys) := by
  induction xs generalizing ys with
  | nil => simp [listLCP]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listLCP]
    | cons y ys =>
      by_cases h : x = y
      · subst h
        have hlcp : listLCP (x :: xs) (x :: ys) = listLCP xs ys + 1 := by
          simp [listLCP, add_comm]
        rw [hlcp]
        simp
        rw [ih ys]
      · simp [listLCP, h]

/-- If the first `k` elements of `xs` and `ys` agree (and `k` is within bounds),
then `k` is at most the LCP of `xs` and `ys`. -/
lemma listLCP_ge_of_take_eq {α : Type u} [DecidableEq α] (xs ys : List α) (k : Nat)
    (h : xs.take k = ys.take k) (hk1 : k ≤ xs.length) (hk2 : k ≤ ys.length) :
    k ≤ listLCP xs ys := by
  induction' k with k ih generalizing xs ys
  · exact Nat.zero_le _
  · cases xs with
    | nil => simp at hk1
    | cons x xs =>
      cases ys with
      | nil => simp at hk2
      | cons y ys =>
        have htake : (x :: xs).take (k + 1) = x :: xs.take k := by simp
        have htake' : (y :: ys).take (k + 1) = y :: ys.take k := by simp
        rw [htake, htake'] at h
        rcases List.cons.inj h with ⟨hx_eq_y, h_tails⟩
        subst hx_eq_y
        simp only [List.length_cons] at hk1 hk2
        have hk1' : k ≤ xs.length := by omega
        have hk2' : k ≤ ys.length := by omega
        simp [listLCP]
        have hk_le : k ≤ listLCP xs ys := ih xs ys h_tails hk1' hk2'
        omega

/-! ### Maximum LCP with suffixes and longest common sublist -/

/-- For a fixed list `l1`, compute the maximum `listLCP l1 (l2.drop j)` over all `j`.
This is the longest prefix match of `l1` against any suffix of `l2`. -/
def maxLCPWithSuffix {α : Type u} [DecidableEq α] : List α → List α → Nat
  | _, [] => 0
  | l1, (b :: bs) =>
      Nat.max (listLCP l1 (b :: bs)) (maxLCPWithSuffix l1 bs)

/-- The prefix match of `l1` against any particular suffix of `l2` is at most `maxLCPWithSuffix l1 l2`. -/
lemma maxLCPWithSuffix_le {α : Type u} [DecidableEq α] (l1 l2 : List α) (j : Nat) :
    listLCP l1 (l2.drop j) ≤ maxLCPWithSuffix l1 l2 := by
  induction l2 generalizing l1 j with
  | nil =>
    cases l1 <;> simp [maxLCPWithSuffix, listLCP]
  | cons b bs ih =>
    rw [maxLCPWithSuffix]
    cases j with
    | zero =>
      simp only [List.drop_zero]
      apply Nat.le_max_left
    | succ j' =>
      have h := ih l1 j'
      have drop_eq : (b :: bs).drop (j' + 1) = bs.drop j' := by simp
      rw [drop_eq]
      exact le_trans h (Nat.le_max_right _ _)

/-- Length of the longest common contiguous segment of two lists.
This is the maximum of `listLCP (l1.drop i) (l2.drop j)` over all `i, j`.
Also known as the "longest common subarray" or "longest common substring" problem. -/
def longestCommonSublistLength {α : Type u} [DecidableEq α] : List α → List α → Nat
  | [], _ => 0
  | (a :: as), l2 =>
      Nat.max (maxLCPWithSuffix (a :: as) l2) (longestCommonSublistLength as l2)

end List

namespace List

/-! ### Sublist extraction -/

/-- Extract a contiguous sublist from `l` starting at index `i` with length `len`.
Returns `[]` if `i` is out of bounds or `len` is `0`. -/
def sublist (l : List α) (i len : Nat) : List α :=
  (l.drop i).take len


lemma sublist_of_nil (i len : Nat) : sublist ([] : List α) i len = [] := by
  simp [sublist]


lemma sublist_length_zero (l : List α) (i : Nat) : sublist l i 0 = [] := by
  simp [sublist]

/-- The length of `List.sublist l i len` is `len` when `i + len ≤ l.length`. -/
lemma sublist_length {α : Type} (l : List α) (i len : Nat) (h : i + len ≤ l.length) :
    (l.sublist i len).length = len := by
  unfold sublist
  have h_drop_len : (l.drop i).length = l.length - i := by
    simp [List.length_drop]
  have h_len_le : len ≤ (l.drop i).length := by
    rw [h_drop_len]
    omega
  exact List.length_take_of_le h_len_le

/-- Extract a contiguous slice from `l` from index `i` to index `j` (inclusive).
If `j < i`, the result is `[]` (due to truncated subtraction).
This differs from `sublist l i len` which takes a start index and length;
`slice l i j` is equivalent to `sublist l i (j - i + 1)`. -/
def slice (l : List α) (i j : Nat) : List α :=
  (l.drop i).take (j - i + 1)

/-- Left-fold a binary operation `op` with initial value `init` over the contiguous slice
from index `i` to index `j` (inclusive) in `l`. When `j < i`, the subarray is empty
(since `j - i + 1` truncates to `0` in `Nat`), so the result is `init`.

This generalizes both `sliceSum` (fold `(+)` with `init = 0`) and `sliceMin` (fold `Nat.min`).
`sliceFoldl op init l i j` is equivalent to `(slice l i j).foldl op init`. -/
def sliceFoldl {α : Type} (op : α → α → α) (init : α) (l : List α) (i j : Nat) : α :=
  ((l.drop i).take (j - i + 1)).foldl op init

/-- Sum of a contiguous slice from index `i` to index `j` (inclusive) in `l`.
Equivalent to `(slice l i j).sum`. If `j < i`, the result is `0` (due to truncated subtraction
making `take` return `[]`). Generalized to any `AddCommMonoid α`. -/
def sliceSum {α : Type} [AddCommMonoid α] (l : List α) (i j : Nat) : α :=
  (slice l i j).sum


lemma sliceSum_nil {α : Type} [AddCommMonoid α] (i j : Nat) : sliceSum ([] : List α) i j = 0 := by
  simp [sliceSum, slice]

/-! ### Minimum of a contiguous slice -/

/-- Minimum element of a contiguous slice from index `i` to index `j` (inclusive) in `l`.
Returns `0` for the empty case (which occurs when `j < i` or `i` is out of bounds).
Equivalent to `(slice l i j).foldl Nat.min h` for the first element `h`, or `0` if empty. -/
def sliceMin (l : List Nat) (i j : Nat) : Nat :=
  match slice l i j with
  | [] => 0
  | h :: t => List.foldl (fun a b => Nat.min a b) h t


lemma sliceMin_nil (i j : Nat) : sliceMin ([] : List Nat) i j = 0 := by
  simp [sliceMin, slice]

/-! ### All contiguous sublists -/

/-- Returns all contiguous sublists of a list. Each sublist has length at least 1.
For example, `contiguousSublists [1,2,3] = [[1],[1,2],[1,2,3],[2],[2,3],[3]]`. -/
def contiguousSublists (l : List α) : List (List α) :=
  let n := l.length
  (List.range n).flatMap fun i =>
    (List.range (n - i)).map fun len => (l.drop i).take (len + 1)

/-- The empty list has no contiguous sublists (since every sublist has length ≥ 1). -/

theorem contiguousSublists_nil : contiguousSublists ([] : List α) = [] := by
  unfold contiguousSublists; simp

/-! ### Window sum — sum of a contiguous sublist -/

/-- Sum of a contiguous window of `len` elements starting at index `i` in `l`.
Equivalent to `(sublist l i len).sum`.
Generalized to any `AddCommMonoid α` — for `Nat` this is the sum of `len` consecutive
elements beginning at position `i`. -/
def windowSum {α : Type} [AddCommMonoid α] (l : List α) (i len : Nat) : α :=
  (sublist l i len).sum


lemma windowSum_nil {α : Type} [AddCommMonoid α] (i len : Nat) : windowSum ([] : List α) i len = 0 := by
  simp [windowSum, sublist]

/-- `windowSum` equals `List.sum` of the `sublist` obtained by dropping `i` and taking `len`. -/
lemma windowSum_eq_sublist_sum {α : Type} [AddCommMonoid α] (l : List α) (i len : Nat) :
    windowSum l i len = (sublist l i len).sum :=
  rfl

/-! ### Range sum — sum via index-based access with zero padding -/

/-- Sum of `len` consecutive elements of `l` starting at index `start`,
using index-based access with `getD 0` for out-of-bounds positions.
This differs from `windowSum` in that OOB positions contribute `0`
rather than being truncated. When `start + len ≤ l.length`, the two agree. -/
def sumRange (l : List Nat) (start : Nat) (len : Nat) : Nat :=
  (List.range len).foldl (fun acc i => acc + (l[start + i]?).getD 0) 0


lemma sumRange_nil (start len : Nat) : sumRange ([] : List Nat) start len = 0 := by
  simp [sumRange]


lemma sumRange_zero_len (l : List Nat) (start : Nat) : sumRange l start 0 = 0 := by
  simp [sumRange]

/-- When the range is fully within bounds, `sumRange` equals `windowSum`. -/
lemma sumRange_eq_windowSum (l : List Nat) (start len : Nat) (h : start + len ≤ l.length) :
    sumRange l start len = windowSum l start len := by
  have fold (xs : List Nat) (f : Nat → Nat) (a : Nat) :
      xs.foldl (fun acc i => acc + f i) a = a + (xs.map f).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons, ih, Nat.add_assoc]
  have entries (xs : List Nat) (n : Nat) (hn : n ≤ xs.length) :
      (List.range n).map (fun i => (xs[i]?).getD 0) = xs.take n := by
    induction xs generalizing n with
    | nil =>
      have : n = 0 := by simpa using hn
      subst n
      rfl
    | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => simpa [List.range_succ_eq_map, List.map_map] using congrArg (x :: ·) (ih n (by simpa using hn))
  have he := entries (l.drop start) len (by simp only [List.length_drop]; omega)
  simp only [List.getElem?_drop] at he
  simpa [sumRange, windowSum, sublist, fold] using congrArg List.sum he

/-! ### Prefix sum — sum of first `k` elements -/

/-- Sum of the first `k` elements of `l`. Equivalent to `(l.take k).sum`.
Compare with `windowSum l i len` which sums a window starting at `i` with length `len`;
`sumPrefix l k` is `windowSum l 0 k`. -/
def sumPrefix {α : Type} [AddCommMonoid α] (l : List α) (k : Nat) : α :=
  (l.take k).sum


lemma sumPrefix_nil {α : Type} [AddCommMonoid α] (k : Nat) : sumPrefix ([] : List α) k = 0 := by
  simp [sumPrefix]

/-- Sum of the first 0 elements is always 0. -/

lemma sumPrefix_zero {α : Type} [AddCommMonoid α] (l : List α) : sumPrefix l 0 = 0 := by
  simp [sumPrefix]

/-- `sumPrefix` of a cons with `k+1` elements decomposes as `a + sumPrefix l k`. -/
lemma sumPrefix_succ {α : Type} [AddCommMonoid α] (a : α) (l : List α) (k : Nat) :
    sumPrefix (a :: l) (k + 1) = a + sumPrefix l k := by
  simp [sumPrefix, List.take_succ_cons]

/-! ### Sliding window maximum count -/

/-- Returns the maximum count of elements satisfying predicate `p` in any
contiguous window of length `k` in list `xs`. Returns `0` if `xs` is shorter than `k`. -/
def maxSlidingCount {α : Type} (p : α → Bool) (xs : List α) (k : Nat) : Nat :=
  if xs.length < k then
    0
  else
    match xs with
    | [] => 0
    | _ :: xs' =>
      max (List.countP p (xs.take k)) (maxSlidingCount p xs' k)

/-! ### Segment fold — fold over a contiguous sublist -/

/-- Fold a binary operation `f` over a contiguous segment of `as` starting at index `start`
and taking at most `len` elements. Returns `init` if the segment is empty or `start`
is past the end of the list.

This generalizes `windowSum`: where `windowSum` only sums, `segmentFoldl` applies
an arbitrary fold `f` with initial value `init`. -/
def segmentFoldl (f : α → α → α) (init : α) (as : List α) (start len : Nat) : α :=
  (sublist as start len).foldl f init

/-- `segmentFoldl` returns `init` when taking zero elements from any list. -/

lemma segmentFoldl_zero_len (f : α → α → α) (init : α) (as : List α) (start : Nat) :
    segmentFoldl f init as start 0 = init := by
  simp [segmentFoldl, sublist]

/-- `segmentFoldl` returns `init` when the list is empty. -/

lemma segmentFoldl_nil (f : α → α → α) (init : α) (start len : Nat) :
    segmentFoldl f init [] start len = init := by
  simp [segmentFoldl, sublist]

/-- `segmentFoldl` returns `init` when `start` is at or past the end of the list. -/
lemma segmentFoldl_start_ge_length (f : α → α → α) (init : α) (as : List α) (start len : Nat)
    (h : as.length ≤ start) : segmentFoldl f init as start len = init := by
  have hdrop : as.drop start = [] := List.drop_eq_nil_of_le h
  simp [segmentFoldl, sublist, hdrop]

/-- When `len` is large enough that the segment extends past the end of the list,
`segmentFoldl` is equivalent to taking all remaining elements. -/
lemma segmentFoldl_len_ge_remaining (f : α → α → α) (init : α) (as : List α) (start len : Nat)
    (h : as.length - start ≤ len) : segmentFoldl f init as start len = segmentFoldl f init as start (as.length - start) := by
  have hdrop_len : (as.drop start).length = as.length - start := List.length_drop start as
  have htake_len : (as.drop start).take len = as.drop start :=
    List.take_of_length_le (hdrop_len ▸ h)
  have htake_rem : (as.drop start).take (as.length - start) = as.drop start :=
    List.take_of_length_le (hdrop_len ▸ le_refl _)
  simp [segmentFoldl, sublist, htake_len, htake_rem]

end List


namespace List

/-! ### All contiguous subarrays -/

/-- All contiguous subarrays of a list, ordered by start index then length.
    `allSubarrays [1,2,3]` yields `[[1],[1,2],[1,2,3],[2],[2,3],[3]]`. -/
def allSubarrays {α : Type u} (xs : List α) : List (List α) :=
  let n := xs.length
  (List.range n).flatMap fun i =>
    (List.range (n - i)).map fun len =>
      List.take (len + 1) (List.drop i xs)

/-- `allSubarrays` on the empty list is empty. -/
lemma allSubarrays_nil : allSubarrays ([] : List α) = [] := by
  simp [allSubarrays]

/-- `allSubarrays` on a singleton list returns the list containing that singleton. -/
lemma allSubarrays_singleton (x : α) : allSubarrays [x] = [[x]] := by
  simp [allSubarrays, List.range_succ]

/-! ### Sums of all contiguous subarrays -/

/-- Sums of all contiguous subarrays of a list, in the order produced by `allSubarrays`.
    `subarraySums [1,2,3]` yields `[1,3,6,2,5,3]`. -/
def subarraySums {α : Type u} [AddCommMonoid α] (nums : List α) : List α :=
  (allSubarrays nums).map List.sum

/-- `subarraySums` on the empty list is empty. -/
lemma subarraySums_nil {α : Type u} [AddCommMonoid α] : subarraySums ([] : List α) = [] := by
  simp [subarraySums, allSubarrays_nil]

/-! ### All subarray values as a Finset -/

/-- The finite set of all values obtained by applying `f` to all valid subarray index pairs
`(l, r)` with `l ≤ r` and both indices within bounds of `xs`.

This is a general combinator: given a function `f l r xs` that computes a value from a subarray
of `xs` delimited by indices `l` and `r` (inclusive), `allSubarrayValues f xs` returns the
`Finset` of all such values over every contiguous subarray.

Useful for problems that need to compute the maximum (or minimum, or sum, etc.) over all
subarray values, e.g., "maximum min-product over all subarrays". -/
def allSubarrayValues {α β : Type u} [DecidableEq β] (f : Nat → Nat → List α → β) (xs : List α) :
    Finset β :=
  (Finset.subarrayIndexPairs (List.length xs)).image (λ ⟨l, r⟩ => f l r xs)

/-! ### Existence of a contiguous subarray satisfying a predicate -/

/-- Check if there exists a contiguous subarray of length `len` in `xs`
satisfying the boolean property `P`. -/
def hasSubarray (P : List α → Bool) (xs : List α) (len : Nat) : Bool :=
  let n := xs.length
  (List.range n).any (λ i =>
    if i + len ≤ n then
      P ((xs.drop i).take len)
    else false)

/-- General lemma: `hasSubarray P xs len` returns true iff there exists
a contiguous subarray of `xs` of length `len` such that `P` holds. -/
lemma hasSubarray_iff (P : List α → Bool) (xs : List α) (len : Nat) (hlen : 0 < len) :
    (hasSubarray P xs len = true) ↔
    (∃ i, i + len ≤ xs.length ∧ P ((xs.drop i).take len) = true) := by
  unfold hasSubarray
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi_mem, hi⟩
    have hi_lt : i < xs.length := by
      simpa [List.mem_range] using hi_mem
    by_cases hcond : i + len ≤ xs.length
    · simp [hcond] at hi
      exact ⟨i, hcond, hi⟩
    · simp [hcond] at hi
  · rintro ⟨i, hi_le, hP⟩
    have hi_lt : i < xs.length := by omega
    have hcond_bool : (i + len ≤ xs.length) = true := by
      simpa using hi_le
    refine ⟨i, List.mem_range.mpr hi_lt, ?_⟩
    simp [hcond_bool, hP]

/-! ### Count sliding windows satisfying a predicate -/

/-- Count the number of sliding windows of length `k` in `l` that satisfy predicate `p`. -/
def countWindowsWhere {α : Type} (k : Nat) (l : List α) (p : List α → Bool) : Nat :=
  if k = 0 then 0 else
  let n := l.length
  (List.range (n + 1 - k)).foldl (fun acc i =>
    if p ((l.drop i).take k) then acc + 1 else acc) 0

/-- Count the number of sliding window starting positions `i` where `pred i` holds.
Valid starting positions are `0 ≤ i ≤ xs.length - windowSize` (i.e., windows that fit
entirely within `xs`). Returns `0` if `windowSize > xs.length` (via truncated subtraction).
Unlike `countWindowsWhere`, this takes an index predicate rather than extracting sublists,
making it more efficient when you only need to check starting positions. -/
def countWindows {α : Type} (xs : List α) (windowSize : Nat) (pred : Nat → Bool) : Nat :=
  ((List.range (xs.length - windowSize)).filter pred).length

lemma countWindows_nil {α : Type} (k : Nat) (pred : Nat → Bool) :
    countWindows ([] : List α) k pred = 0 := by
  simp [countWindows]

lemma countWindows_zero (xs : List α) (pred : Nat → Bool) :
    countWindows xs 0 pred = ((List.range xs.length).filter pred).length := by
  simp [countWindows]

/-! ### Element-level sliding window checks -/

/-- Check whether all elements in a window of length `k` starting at index `i`
in `xs` satisfy predicate `p`. Returns `false` if the window extends past
the end of the list.

Uses `drop`/`take` for extraction to avoid `Inhabited` constraints. -/
def windowAll {α : Type} (xs : List α) (k i : Nat) (p : α → Bool) : Bool :=
  if i + k ≤ xs.length then
    ((xs.drop i).take k).all p
  else
    false

/-- Check whether there exists a starting position `i` such that the window of
length `k` in `xs` satisfies predicate `p` on every element. -/
def existsWindow {α : Type} (xs : List α) (k : Nat) (p : α → Bool) : Bool :=
  (List.range (xs.length + 1)).any fun i => windowAll xs k i p

/-- Check whether a pattern of comparisons between adjacent elements holds at position `i` in `xs`.

Given a comparison function `cmp : β → α → α → Bool`, a pattern list `pattern : List β`, and a
starting index `i`, this checks that for each `k` from `0` to `pattern.length - 1`, the comparison
`cmp pattern[k] xs[i+k] xs[i+k+1]` is `true`.

The window covers `pattern.length + 1` consecutive elements (checking each adjacent pair). Returns
`false` if the window would extend beyond the list bounds or if any index lookups fail.

This is the core building block for problems like LeetCode 3034 "Number of Subarrays That Match
a Pattern", where the pattern encodes comparison operators (e.g., `-1` for `>`, `0` for `=`,
`1` for `<`) and we count windows where those comparisons hold between adjacent elements. -/
def windowMatches {α β : Type} (cmp : β → α → α → Bool) (xs : List α) (pattern : List β) (i : Nat) : Bool :=
  let m := pattern.length
  if i + m + 1 ≤ xs.length then
    (List.range m).all (fun k =>
      match pattern[k]?, xs[i + k]?, xs[i + k + 1]? with
      | some pk, some a, some b => cmp pk a b
      | _, _, _ => false)
  else
    false

/-- Count sliding windows where adjacent element comparisons match a given pattern.
`countPatternWindows cmp xs pattern` counts the number of starting positions `i` such that
for each `k < pattern.length`, the comparison `cmp pattern[k] xs[i+k] xs[i+k+1]` holds.

This is a composition of `countWindows` and `windowMatches`. It generalizes
LeetCode 3034 "Number of Subarrays That Match a Pattern" by parameterizing over the
comparison function rather than hardcoding `-1/0/1` → `>/=/<` on `Nat`. -/
def countPatternWindows {α β : Type} (cmp : β → α → α → Bool) (xs : List α) (pattern : List β) : Nat :=
  countWindows xs (pattern.length) (windowMatches cmp xs pattern)

lemma countPatternWindows_nil {α β : Type} (cmp : β → α → α → Bool) (pattern : List β) :
    countPatternWindows cmp ([] : List α) pattern = 0 := by
  simp [countPatternWindows, countWindows]

/-! ### Maximum length of a contiguous subarray satisfying a predicate -/

/-- Recursively compute the maximum length (up to `k`) of a contiguous subarray of `xs`
satisfying property `P`. -/
def maxSubarrayLenAux (P : List α → Bool) (xs : List α) (k : Nat) : Nat :=
  if k = 0 then 0
  else
    let prev := maxSubarrayLenAux P xs (k - 1)
    if hasSubarray P xs k then max prev k else prev
termination_by k

/-- Compute the maximum length of a contiguous subarray of `xs` satisfying property `P`. -/
def maxSubarrayLen (P : List α → Bool) (xs : List α) : Nat :=
  maxSubarrayLenAux P xs xs.length

/-- General specification for `maxSubarrayLenAux`:
the result is bounded by `k`, it is sound (any length ≤ k with the property
is ≤ the result), and it is complete (the result itself has the property
or is zero). -/
lemma maxSubarrayLenAux_spec (P : List α → Bool) (xs : List α) (k : Nat) :
    maxSubarrayLenAux P xs k ≤ k ∧
    (∀ len, 1 ≤ len → len ≤ k → hasSubarray P xs len = true →
      len ≤ maxSubarrayLenAux P xs k) ∧
    (maxSubarrayLenAux P xs k = 0 ∨
      (1 ≤ maxSubarrayLenAux P xs k ∧
       hasSubarray P xs (maxSubarrayLenAux P xs k) = true)) := by
  induction' k with m ih
  · -- k = 0
    unfold maxSubarrayLenAux
    refine ⟨by simp, ?_, by simp⟩
    intro len hlen1 hlen0 _
    omega
  · -- k = m+1
    rcases ih with ⟨h_bound, h_max, h_witness⟩
    unfold maxSubarrayLenAux
    have hsub : (m + 1 : Nat) - 1 = m := by omega
    simp [hsub]
    by_cases hm : hasSubarray P xs (m + 1) = true
    · -- hm : hasSubarray P xs (m + 1) = true
      rw [hm]
      dsimp
      have h_bound' : max (maxSubarrayLenAux P xs m) (m + 1) ≤ m + 1 := by
        apply max_le
        · exact Nat.le_succ_of_le h_bound
        · rfl
      have h_max' : ∀ len, 1 ≤ len → len ≤ m + 1 → hasSubarray P xs len = true →
          len ≤ max (maxSubarrayLenAux P xs m) (m + 1) := by
        intro len hlen1 hlen_m1 hlen_prop
        rcases Nat.eq_or_lt_of_le hlen_m1 with (rfl | hlen_lt)
        · exact Nat.le_max_right _ _
        · have hle_m : len ≤ m := by omega
          have hle_prev : len ≤ maxSubarrayLenAux P xs m :=
            h_max len hlen1 hle_m hlen_prop
          exact le_trans hle_prev (Nat.le_max_left _ _)
      have hmax_ge1 : 1 ≤ max (maxSubarrayLenAux P xs m) (m + 1) := by
        have hpos : 1 ≤ m + 1 := by omega
        exact le_trans hpos (Nat.le_max_right _ _)
      have hwitness : hasSubarray P xs
          (max (maxSubarrayLenAux P xs m) (m + 1)) = true := by
        have h_lt : maxSubarrayLenAux P xs m < m + 1 := by omega
        have hmax_eq : max (maxSubarrayLenAux P xs m) (m + 1) = m + 1 :=
          Nat.max_eq_right (Nat.le_of_lt h_lt)
        rw [hmax_eq]
        exact hm
      refine ⟨h_bound', h_max', Or.inr ⟨hmax_ge1, hwitness⟩⟩
    · -- hm : ¬ hasSubarray P xs (m + 1) = true
      have hm_false : hasSubarray P xs (m + 1) = false :=
        Bool.eq_false_of_not_eq_true hm
      rw [hm_false]
      dsimp
      have h_bound' : maxSubarrayLenAux P xs m ≤ m + 1 :=
        Nat.le_succ_of_le h_bound
      have h_max' : ∀ len, 1 ≤ len → len ≤ m + 1 → hasSubarray P xs len = true →
          len ≤ maxSubarrayLenAux P xs m := by
        intro len hlen1 hlen_m1 hlen_prop
        rcases Nat.eq_or_lt_of_le hlen_m1 with (rfl | hlen_lt)
        · rw [hm_false] at hlen_prop; simp at hlen_prop
        · have hle_m : len ≤ m := by omega
          exact h_max len hlen1 hle_m hlen_prop
      refine ⟨h_bound', h_max', h_witness⟩

/-- Find the maximum `l ≤ maxLen` such that there exists a contiguous substring
of length `l` in `xs` satisfying the boolean predicate `P`. Returns `0` if no
nonempty such substring exists or if `maxLen = 0`.

This is structurally recursive on `maxLen`, checking from `maxLen` down to `0`.
Unlike `maxSubarrayLenAux`, this does not require a separate `hasSubarray` helper
and directly checks existence via `List.range.any`. -/
def findMaxSubstringLen {α : Type} (P : List α → Bool) (xs : List α) (maxLen : Nat) : Nat :=
  match maxLen with
  | 0 => 0
  | l+1 =>
    if h : l+1 ≤ xs.length then
      if (List.range (xs.length - (l+1) + 1)).any (fun i => P ((xs.drop i).take (l+1))) then
        l+1
      else
        findMaxSubstringLen P xs l
    else
      findMaxSubstringLen P xs l

/--
Combined correctness lemma for `findMaxSubstringLen`:
- result ≤ maxLen
- result is either 0 or witnessed by a substring satisfying P
- no substring longer than result (and ≤ maxLen) satisfies P
-/
lemma findMaxSubstringLen_spec {α : Type} (P : List α → Bool) (xs : List α) (maxLen : Nat) :
    (findMaxSubstringLen P xs maxLen ≤ maxLen) ∧
    ((findMaxSubstringLen P xs maxLen = 0) ∨
     (∃ i, i + (findMaxSubstringLen P xs maxLen) ≤ xs.length ∧
      P ((xs.drop i).take (findMaxSubstringLen P xs maxLen)) = true)) ∧
    (∀ l, (findMaxSubstringLen P xs maxLen) < l → l ≤ maxLen →
      (∀ i, i + l ≤ xs.length → P ((xs.drop i).take l) = false)) := by
  induction maxLen with
  | zero =>
    unfold findMaxSubstringLen
    refine ⟨by decide, Or.inl rfl, ?_⟩
    intro l hl_lt hl_le
    omega
  | succ l ih =>
    simp [findMaxSubstringLen]
    split
    · rename_i h
      split
      · rename_i h_any
        rcases h_any with ⟨i, hi_lt, hi_wf⟩
        have hi_bound : i + (l+1) ≤ xs.length := by omega
        refine ⟨by omega, Or.inr ⟨i, hi_bound, hi_wf⟩, ?_⟩
        intro l' hl'_gt hl'_le i' hi'_bound
        omega
      · rename_i h_any
        have h_any' : ∀ i, i + (l+1) ≤ xs.length → P ((xs.drop i).take (l+1)) = false := by
          intro i hi_bound
          match hh : P ((xs.drop i).take (l+1)) with
          | true =>
            exfalso
            apply h_any
            exact ⟨i, by omega, hh⟩
          | false => rfl
        rcases ih with ⟨ih_le, ih_ex, ih_max⟩
        refine ⟨by omega, ih_ex, ?_⟩
        intro l' hl'_gt hl'_le i' hi'_bound
        have hl'_cases : l' ≤ l ∨ l' = l+1 := by omega
        rcases hl'_cases with (hl'_le_l | hl'_eq)
        · exact ih_max l' hl'_gt hl'_le_l i' hi'_bound
        · have hi'_bound_l1 : i' + (l+1) ≤ xs.length := by
            simpa [hl'_eq] using hi'_bound
          rw [hl'_eq]
          exact h_any' i' hi'_bound_l1
    · rename_i h
      rcases ih with ⟨ih_le, ih_ex, ih_max⟩
      refine ⟨by omega, ih_ex, ?_⟩
      intro l' hl'_gt hl'_le i' hi'_bound
      have hl'_cases : l' ≤ l ∨ l' = l+1 := by omega
      rcases hl'_cases with (hl'_le_l | hl'_eq)
      · exact ih_max l' hl'_gt hl'_le_l i' hi'_bound
      · rw [hl'_eq] at hi'_bound
        omega

lemma findMaxSubstringLen_le_maxLen {α : Type} (P : List α → Bool) (xs : List α) (maxLen : Nat) :
    findMaxSubstringLen P xs maxLen ≤ maxLen :=
  (findMaxSubstringLen_spec P xs maxLen).1

lemma findMaxSubstringLen_zero_or_exists {α : Type} (P : List α → Bool) (xs : List α) (maxLen : Nat) :
    (findMaxSubstringLen P xs maxLen = 0) ∨
    (∃ i, i + (findMaxSubstringLen P xs maxLen) ≤ xs.length ∧
     P ((xs.drop i).take (findMaxSubstringLen P xs maxLen)) = true) :=
  (findMaxSubstringLen_spec P xs maxLen).2.1

lemma findMaxSubstringLen_maximal {α : Type} (P : List α → Bool) (xs : List α) (maxLen : Nat) :
    ∀ l, (findMaxSubstringLen P xs maxLen) < l → l ≤ maxLen →
      (∀ i, i + l ≤ xs.length → P ((xs.drop i).take l) = false) :=
  (findMaxSubstringLen_spec P xs maxLen).2.2

/-! ### Maximum subarray sum (Kadane's algorithm) -/

/-- Maximum subarray sum computed via Kadane's algorithm over a list of elements
from a linearly ordered additive commutative monoid. Returns `0` for the empty list.

The algorithm maintains the best sum seen so far and the best sum ending at the current
position, updating both as it scans the list. This runs in O(n) time. -/
def maxSubarraySum {α : Type} [LinearOrderedAddCommMonoid α] (xs : List α) : α :=
  match xs with
  | [] => 0
  | x :: xs' =>
    let f : α × α → α → α × α :=
      fun (best, cur) y =>
        let cur'  := max y (cur + y)
        let best' := max best cur'
        (best', cur')
    let (best, _) := xs'.foldl f (x, x)
    best

/-! ### Kadane's algorithm with projection function

These variants accept a projection function `f : α → Int`, making them useful when
you have a list of objects and want the maximum subarray sum of some integer-valued
property. Compare with `maxSubarraySum` which works directly on the list elements. -/

/-- Invariant maintained throughout Kadane's algorithm:
`best` (the best sum seen so far) is nonnegative and at least `cur`
(the best sum ending at the current position). -/
structure KadaneState (cur best : Int) : Prop where
  h_nonneg : 0 ≤ best
  h_ge_cur : cur ≤ best

/-- Maximum subarray sum of `f` over a list via Kadane's algorithm (iterative `foldl`).
Finds the maximum value of `∑ f a` over any contiguous sublist of `L`.
Returns `0` for the empty list (the empty subarray has sum 0).
This runs in O(n) time. -/
def maxSubarraySumOf {α : Type} (f : α → Int) (L : List α) : Int :=
  let init : Int × Int := (0, 0)
  let final :=
    L.foldl
      (fun acc a =>
        let v := f a
        let cur := acc.1
        let best := acc.2
        let cur' := max (cur + v) v
        let best' := max best cur'
        (cur', best'))
      init
  final.2

/-- Recursive formulation of Kadane's algorithm with a projection function,
convenient for induction proofs. The pair `(cur, best)` tracks the current
running sum and the best sum seen so far. -/
def maxSubarraySumOfRec {α : Type} (f : α → Int) (L : List α) (cur best : Int) : Int × Int :=
  match L with
  | [] => (cur, best)
  | a :: rest =>
    let v := f a
    let cur' := max (cur + v) v
    let best' := max best cur'
    maxSubarraySumOfRec f rest cur' best'

/-! ### Maximum prefix sum -/

/-- Maximum prefix sum of a list, computed right-to-left by recursion.
Returns the maximum sum of any prefix (including the empty prefix, which gives `0`).
For a non-empty list, the max prefix sum of `x::xs` is either `x` alone or
`x` plus the max prefix sum of `xs`.
Defines `maxPrefixSum [] = 0`, `maxPrefixSum [x] = x`,
`maxPrefixSum (x::y::xs) = max x (x + maxPrefixSum (y::xs))`. -/
def maxPrefixSum {α : Type} [LinearOrderedAddCommMonoid α] : List α → α
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
    max x (x + maxPrefixSum (y :: xs))

/-- Any prefix sum is bounded above by `maxPrefixSum`. -/
lemma maxPrefixSum_upper {α : Type} [LinearOrderedAddCommMonoid α] (nums : List α) (k : Nat)
    (hk : k < nums.length) : sliceSum nums 0 k ≤ maxPrefixSum nums := by
  match nums with
  | [] => simp at hk
  | [x] =>
    have : k = 0 := by simpa using hk
    simp [this, sliceSum, slice, maxPrefixSum]
  | x :: y :: xs =>
    cases k with
    | zero => simpa [sliceSum, slice, maxPrefixSum] using le_max_left x (x + maxPrefixSum (y :: xs))
    | succ k =>
      have ih := maxPrefixSum_upper (y :: xs) k (by simpa using hk)
      have h := (add_le_add_left ih x).trans (le_max_right x (x + maxPrefixSum (y :: xs)))
      simpa [sliceSum, slice, maxPrefixSum] using h

/-- If `nums` is nonempty, then `maxPrefixSum` is achieved by some prefix. -/
lemma maxPrefixSum_achieved {α : Type} [LinearOrderedAddCommMonoid α] (nums : List α) (hne : nums ≠ []) :
    ∃ k, k < nums.length ∧ sliceSum nums 0 k = maxPrefixSum nums := by
  match nums with
  | [] => contradiction
  | [x] => exact ⟨0, by simp, by simp [sliceSum, slice, maxPrefixSum]⟩
  | x :: y :: xs =>
    by_cases h : x + maxPrefixSum (y :: xs) ≤ x
    · exact ⟨0, by simp, by simp [sliceSum, slice, maxPrefixSum, max_eq_left h]⟩
    · obtain ⟨k, hk, he⟩ := maxPrefixSum_achieved (y :: xs) (by simp)
      refine ⟨k+1, by simpa using hk, ?_⟩
      simpa [sliceSum, slice, maxPrefixSum, max_eq_right (le_of_not_ge h)] using congrArg (x + ·) he

/-! ### Minimum prefix sum -/

/-- Minimum prefix sum of a list, computed right-to-left by recursion.
Returns the minimum sum of any prefix (including the empty prefix, which gives `0`).
Defines `minPrefixSum [] = 0`, `minPrefixSum [x] = x`,
`minPrefixSum (x::y::xs) = min x (x + minPrefixSum (y::xs))`. -/
def minPrefixSum {α : Type} [LinearOrderedAddCommMonoid α] : List α → α
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
    min x (x + minPrefixSum (y :: xs))

/-- Any prefix sum is bounded below by `minPrefixSum`. -/
lemma minPrefixSum_lower {α : Type} [LinearOrderedAddCommMonoid α] (nums : List α) (k : Nat)
    (hk : k < nums.length) : minPrefixSum nums ≤ sliceSum nums 0 k := by
  match nums with
  | [] => simp at hk
  | [x] =>
    have : k = 0 := by simpa using hk
    simp [this, sliceSum, slice, minPrefixSum]
  | x :: y :: xs =>
    cases k with
    | zero => simpa [sliceSum, slice, minPrefixSum] using min_le_left x (x + minPrefixSum (y :: xs))
    | succ k =>
      have ih := minPrefixSum_lower (y :: xs) k (by simpa using hk)
      have h := (min_le_right x (x + minPrefixSum (y :: xs))).trans (add_le_add_left ih x)
      simpa [sliceSum, slice, minPrefixSum] using h

/-- If `nums` is nonempty, then `minPrefixSum` is achieved by some prefix. -/
lemma minPrefixSum_achieved {α : Type} [LinearOrderedAddCommMonoid α] (nums : List α) (hne : nums ≠ []) :
    ∃ k, k < nums.length ∧ sliceSum nums 0 k = minPrefixSum nums := by
  match nums with
  | [] => contradiction
  | [x] => exact ⟨0, by simp, by simp [sliceSum, slice, minPrefixSum]⟩
  | x :: y :: xs =>
    by_cases h : x ≤ x + minPrefixSum (y :: xs)
    · exact ⟨0, by simp, by simp [sliceSum, slice, minPrefixSum, min_eq_left h]⟩
    · obtain ⟨k, hk, he⟩ := minPrefixSum_achieved (y :: xs) (by simp)
      refine ⟨k+1, by simpa using hk, ?_⟩
      simpa [sliceSum, slice, minPrefixSum, min_eq_right (le_of_not_ge h)] using congrArg (x + ·) he

/-! ### Count subarrays by index predicate -/

/-- Count the number of contiguous subarrays defined by index pairs `(i, j)` with
`0 ≤ i ≤ j < l.length` such that the boolean index predicate `p i j` holds.
This counts subarray intervals directly by index, without extracting sublists.
For counting by sublist content, see `countSubarraysWhere`.
For the `Nat`-based version, see `Nat.countPairs`. -/
def countSubarraysWhereIdx {α : Type} (l : List α) (p : Nat → Nat → Bool) : Nat :=
  (List.range l.length).foldl
    (fun acc i =>
      acc + (List.range (l.length - i)).foldl
        (fun acc' offset =>
          if p i (i + offset) then acc' + 1 else acc')
        0)
    0

/-- Unfold lemma for `countSubarraysWhereIdx`.
Expands the definition for rewriting purposes.
This lemma is fully general: it works for any type `α`, any list `l`, and any predicate `p`. -/
lemma countSubarraysWhereIdx_eq {α : Type} (l : List α) (p : Nat → Nat → Bool) :
    countSubarraysWhereIdx l p =
    (List.range l.length).foldl
      (fun acc i =>
        acc + (List.range (l.length - i)).foldl
          (fun acc' offset => if p i (i + offset) then acc' + 1 else acc')
          0)
      0 := rfl

/-! ### Count substrings by sublist predicate -/

/-- Count the number of contiguous substrings of `l` that satisfy predicate `p`.
Iterates over all `(i, len)` such that `i + len ≤ l.length` and counts
how many substrings `l.drop i |>.take len` satisfy `p`.
This counts substrings at the sublist level (including the empty substring at each
position where `len = 0`), as opposed to `countSubarraysWhere` which counts non-empty
contiguous subarrays. For counting by index predicate, see `countSubarraysWhereIdx`. -/
def countSubstringsWhere {α : Type} (p : List α → Prop) [DecidablePred p] (l : List α) : Nat :=
  (List.range l.length).foldl
    (fun acc i =>
      acc +
        (List.range (l.length - i)).foldl
          (fun acc' len =>
            if p ((l.drop i).take len) then acc' + 1 else acc')
          0)
    0

/-- `countSubstringsWhere` on the empty list is always `0`. -/

lemma countSubstringsWhere_nil {α : Type} (p : List α → Prop) [DecidablePred p] :
    countSubstringsWhere p ([] : List α) = 0 := by
  simp [countSubstringsWhere]

/-! ### Minimum subarray sum (recursive) -/

/-- Minimum subarray sum of a non-empty list, computed right-to-left.
The min subarray sum of `x::xs` is the minimum of:
- the min prefix sum starting at `x` (computed by `minPrefixSum (x::xs)`)
- the min subarray sum entirely within `xs`
Defines `minSubarraySum [] = 0`, `minSubarraySum [x] = x`,
`minSubarraySum (x::y::ys) = min (minPrefixSum (x::y::ys)) (minSubarraySum (y::ys))`. -/
def minSubarraySum {α : Type} [LinearOrderedAddCommMonoid α] : List α → α
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
    min (minPrefixSum (x :: y :: xs)) (minSubarraySum (y :: xs))

/-- Any subarray sum is bounded below by `minSubarraySum`. -/
lemma minSubarraySum_lower {α : Type} [LinearOrderedAddCommMonoid α] (nums : List α) (i j : Nat)
    (hij : i ≤ j) (hj : j < nums.length) : minSubarraySum nums ≤ sliceSum nums i j := by
  match nums with
  | [] => simp at hj
  | [x] =>
    have : j = 0 := by simpa using hj
    have : i = 0 := by omega
    simp_all [sliceSum, slice, minSubarraySum]
  | x :: y :: xs =>
    cases i with
    | zero => exact (min_le_left _ _).trans (minPrefixSum_lower (x :: y :: xs) j hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have ih := minSubarraySum_lower (y :: xs) i j (by omega) (by simpa using hj)
        have h := (min_le_right (minPrefixSum (x :: y :: xs)) (minSubarraySum (y :: xs))).trans ih
        simpa [minSubarraySum, sliceSum, slice] using h

/-! ### Basic subarray extraction via drop/take -/

/-- Extract a contiguous subarray of `nums` starting at index `i` with length `k`.
`subarray nums i k = (nums.drop i).take k`. Equivalent to `nums[i..i+k]` in array notation. -/
def subarray {α : Type} (nums : List α) (i k : Nat) : List α :=
  (nums.drop i).take k

/-- Sum of elements in the subarray of `nums` starting at index `i` with length `k`.
`subarray_sum nums i k = (subarray nums i k).sum`. -/
def subarray_sum {α : Type} [AddCommMonoid α] (nums : List α) (i k : Nat) : α :=
  (subarray nums i k).sum

/-- Extract the contiguous slice `s[i..j]` (inclusive). Returns `[]` when `i > j`.
Uses `(j + 1) - i` as the length to correctly handle `i > j` (Nat subtraction gives `0`).
Equivalent to `subarray s i ((j + 1) - i)`. -/
def subarrayInclusive {α : Type} (s : List α) (i j : Nat) : List α :=
  (s.drop i).take ((j + 1) - i)

/-- `subarrayInclusive` in terms of `subarray`: `subarrayInclusive s i j = subarray s i ((j + 1) - i)`. -/
lemma subarrayInclusive_eq_subarray {α : Type} (s : List α) (i j : Nat) :
    subarrayInclusive s i j = subarray s i ((j + 1) - i) := rfl

lemma subarrayInclusive_nil {α : Type} (i j : Nat) :
    subarrayInclusive ([] : List α) i j = [] := by
  simp [subarrayInclusive]

/-- Taking the inclusive slice from `0` to `l.length - 1` returns the whole list.
This holds even when `l` is empty: for `l = []`, `0-1 = 0` (Nat subtraction), so
`subarrayInclusive [] 0 0 = []`. -/
lemma subarrayInclusive_zero_to_last {α : Type} (l : List α) :
    subarrayInclusive l 0 (l.length - 1) = l := by
  unfold subarrayInclusive
  rw [List.drop_zero]
  simp
  omega

/-! ### Subarray product (inclusive indices) -/

/-- Product of the contiguous subarray from index `i` to `j` (inclusive).
`subProd nums i j = ((nums.drop i).take (j - i + 1)).prod`.
When `i ≤ j`, this is the product of `nums[i] * nums[i+1] * ... * nums[j]`.
When `i > j`, `j - i = 0` (Nat subtraction truncation) so the result is `nums[i]`. -/
def subProd {α : Type} [Monoid α] (nums : List α) (i j : Nat) : α :=
  ((nums.drop i).take (j - i + 1)).prod

/-- When the subarray extends to the end of the list (`j = length - 1`),
`subProd p i (p.length - 1)` equals the product of `p.drop i`. -/
lemma subProd_prefix_drop_eq {α : Type} [Monoid α] (p : List α) (i : Nat) (hi : i < p.length) :
    subProd p i (p.length - 1) = (p.drop i).prod := by
  unfold subProd
  have h_eq_len : (p.length - 1) - i + 1 = p.length - i := by omega
  rw [h_eq_len]
  have h_take_drop_all : (p.drop i).take (p.length - i) = p.drop i :=
    List.take_of_length_le (by
      simp [List.length_drop])
  rw [h_take_drop_all]

/-! ### Weighted segment sum -/

/-- Weighted sum of a contiguous segment of `xs` starting at index `i` with length `len`,
using weight function `w`. `segmentSum xs w i len = ((xs.drop i).take len).map w |>.sum`.

This is like `subarray_sum` but allows a weight function `w : α → β` to be applied to
each element before summing. For example, you can sum `Nat` weights even when `α` itself
is not an `AddCommMonoid`. -/
def segmentSum {α β : Type} [AddCommMonoid β] (xs : List α) (w : α → β) (i len : Nat) : β :=
  ((xs.drop i).take len).map w |>.sum

lemma segmentSum_nil {α β : Type} [AddCommMonoid β] (w : α → β) (i len : Nat) :
    segmentSum ([] : List α) w i len = 0 := by
  simp [segmentSum]

lemma segmentSum_len_zero {α β : Type} [AddCommMonoid β] (xs : List α) (w : α → β) (i : Nat) :
    segmentSum xs w i 0 = 0 := by
  simp [segmentSum]

/-! ### Basic lemmas about `subarray` -/

/-- `subarray` of an empty list is always empty. -/
lemma subarray_nil {α : Type} (i len : Nat) : subarray ([] : List α) i len = [] := by
  unfold subarray; simp

/-- The length of a subarray is at most the requested length. -/
lemma subarray_length_le {α : Type} (l : List α) (i len : Nat) :
    (subarray l i len).length ≤ len := by
  unfold subarray; simp

/-- A subarray of length 0 is always empty. -/
lemma subarray_len_zero {α : Type} (l : List α) (i : Nat) :
    subarray l i 0 = [] := by
  unfold subarray; simp

/-- Taking the whole list as a subarray starting at index 0 returns the original list. -/
lemma subarray_self {α : Type} (l : List α) : subarray l 0 l.length = l := by
  unfold subarray; simp

/-! ### `slidingWindowMap` — map a function over each fixed-length sliding window -/

/-- Apply `f` to every contiguous sliding window of length `k` in `nums`.
Returns a list of `nums.length - k + 1` results (or `0` if `k > nums.length`,
via truncated subtraction).

For example, `slidingWindowMap [1,2,3,4] 2 List.sum = [3,5,7]`. -/
def slidingWindowMap {α β : Type _} (nums : List α) (k : Nat) (f : List α → β) : List β :=
  (List.range (nums.length - k + 1)).map (fun i => f ((nums.drop i).take k))

/-- The length of `slidingWindowMap` is `nums.length - k + 1`.
This follows directly from `List.length_map` and `List.length_range`. -/
lemma slidingWindowMap_length {α β : Type _} (nums : List α) (k : Nat) (f : List α → β) :
    (slidingWindowMap nums k f).length = nums.length - k + 1 := by
  unfold slidingWindowMap
  simp

/-! ### `slidingWindowMapN` — recursive sliding window with explicit count -/

/-- Apply `f` to `nWindows` successive sliding windows of length `k` from `data`.
Each step takes `data.take k`, applies `f`, then advances by dropping 1 element.
Unlike `slidingWindowMap`, this version takes an explicit window count `nWindows`
and does not check whether windows fit within bounds — it may produce windows that
are shorter than `k` near the end.

This recursive formulation is convenient for inductive proofs and for algorithms
that know the exact number of windows to compute. -/
def slidingWindowMapN (f : List α → β) (data : List α) (k : Nat) (nWindows : Nat) : List β :=
  match nWindows with
  | 0 => []
  | m+1 => f (data.take k) :: slidingWindowMapN f (data.drop 1) k m

/-- The length of `slidingWindowMapN` equals `nWindows`. -/

lemma slidingWindowMapN_length (f : List α → β) (data : List α) (k n : Nat) :
    (slidingWindowMapN f data k n).length = n := by
  induction n generalizing data with
  | zero => rfl
  | succ n ih =>
    simp [slidingWindowMapN, ih]

/-- The `i`-th element (0-indexed) of `slidingWindowMapN` equals `f` applied to
the window beginning at position `i` in `data`, provided `i < nWindows`. -/
lemma slidingWindowMapN_get (f : List α → β) (data : List α) (k n i : Nat) (h : i < n) :
    (slidingWindowMapN f data k n).get ⟨i, by
      simpa [slidingWindowMapN_length] using h⟩ = f ((data.drop i).take k) := by
  revert data i
  induction n with
  | zero =>
    intro data i h
    exfalso; exact Nat.not_lt_zero _ h
  | succ n ih =>
    intro data i h
    cases i
    · simp [slidingWindowMapN, slidingWindowMapN_length]
    · rename_i i
      have hi : i < n := Nat.lt_of_succ_lt_succ h
      simp [slidingWindowMapN, slidingWindowMapN_length]
      have h_eq := ih (data.drop 1) i hi
      simpa [show (data.drop 1).drop i = data.drop (i + 1) by
        simp [List.drop_drop, add_comm]] using h_eq

/-! ### `minOverWindows` — minimum over all sliding windows -/

/-- Minimum of `f` applied to each contiguous sliding window of length `k` in `xs`,
starting from an initial bound `init`. Returns `init` if `k > xs.length` (via
truncated subtraction in `List.range`).

For example, `minOverWindows [3,1,4,1,5] 3 List.sum 999 = 6` (window `[1,4,1]` sums to 6). -/
def minOverWindows {α : Type} (xs : List α) (k : Nat) (f : List α → Nat) (init : Nat) : Nat :=
  (List.range (xs.length - k + 1)).foldl (fun b i => Nat.min b (f ((xs.drop i).take k))) init

/-! ### `sublistMatchesAt` — position-based sublist matching -/

/-- Checks whether the sublist of `s` starting at index `i` matches `src`.
Returns `true` if `src` is empty (vacuous match), or if the first `src.length`
elements after `i` in `s` equal `src` under `==`.

This is analogous to `(s.drop i).startsWith src` but works with `BEq` rather than
requiring `DecidableEq`, making it suitable for types like `String`. -/
def sublistMatchesAt {α : Type u} [BEq α] (s : List α) (i : Nat) (src : List α) : Bool :=
  (s.drop i).take src.length == src

/-- Matching the empty list at any position always succeeds. -/

lemma sublistMatchesAt_nil {α : Type u} [BEq α] (s : List α) (i : Nat) :
    sublistMatchesAt s i ([] : List α) = true := by
  simp [sublistMatchesAt]

/-! ### `maxSubstringLength` — maximum length of a substring satisfying a predicate

This is a declarative (non‑algorithmic) definition: generate all possible substrings
by start index and length, filter those satisfying `p`, and take the max length via `foldl max`.
For an efficient algorithm with early termination, see `findMaxSubstringLen`. -/

/-- Compute the maximum length of a substring of `l` that satisfies predicate `p`.
The substring is extracted via `(l.drop i).take len` for each valid `(i, len)` pair. -/
def maxSubstringLength {α : Type} (l : List α) (p : List α → Bool) : Nat :=
  let n := l.length
  (List.range n).flatMap (λ i =>
    let maxLen := n - i
    (List.range (maxLen + 1)).filter (λ len =>
      p ((l.drop i).take len)))
  |>.foldl (λ best len => max best len) 0

/-- Characterization of membership in the substring‑lengths list: `len` is among the lengths
of substrings starting at some `i` for which `p` holds iff there exists a valid `(i, len)` pair
with `i + len ≤ l.length` and `p ((l.drop i).take len) = true`. -/
lemma mem_maxSubstringLength_lengths_iff {α : Type} (l : List α) (p : List α → Bool) (len : Nat) :
    len ∈ (List.range l.length).flatMap (λ i =>
      let maxLen := l.length - i
      (List.range (maxLen + 1)).filter (λ s =>
        p ((l.drop i).take s))) ↔
    ∃ i, i < l.length ∧ i + len ≤ l.length ∧ p ((l.drop i).take len) = true := by
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨i, hi, hlen⟩
    rw [List.mem_filter] at hlen
    rcases hlen with ⟨hlen_mem, hlen_valid⟩
    rw [List.mem_range] at hi hlen_mem
    have hsum : i + len ≤ l.length := by
      have hlen_le : len ≤ l.length - i :=
        Nat.le_of_lt_succ hlen_mem
      omega
    exact ⟨i, hi, hsum, hlen_valid⟩
  · intro h
    rcases h with ⟨i, hi_lt, hsum, hvalid⟩
    rw [List.mem_flatMap]
    refine ⟨i, ?_, ?_⟩
    · rw [List.mem_range]; exact hi_lt
    · rw [List.mem_filter]
      constructor
      · rw [List.mem_range]
        omega
      · simpa [hvalid]

/-! ### `subList` — slice from `start` (inclusive) to `limit` (exclusive)

`subList l start limit` extracts the contiguous segment of `l` from `start`
(inclusive) to `limit` (exclusive). Equivalent to `subarray l start (limit - start)`.

This mirrors Python-style slice `l[start:limit]`. The length is `limit - start` (Nat
subtraction gives `0` when `start ≥ limit`). -/

/-- Extract the contiguous segment of `l` from `start` (inclusive) to `limit` (exclusive).
`subList l start limit = l.drop start |>.take (limit - start)`. -/
def subList (l : List α) (start limit : Nat) : List α :=
  (l.drop start).take (limit - start)

/-- `subList` in terms of `subarray`: `subList l start limit = subarray l start (limit - start)`. -/
lemma subList_eq_subarray (l : List α) (start limit : Nat) :
    subList l start limit = subarray l start (limit - start) := rfl

/-- `subList` of an empty list is always empty. -/

lemma subList_nil (start limit : Nat) : subList ([] : List α) start limit = [] := by
  simp [subList]

/-- `subList` returns empty when `start` is at or beyond the list length. -/
lemma subList_start_ge_length (l : List α) (start limit : Nat) (h : l.length ≤ start) :
    subList l start limit = [] := by
  have hd : l.drop start = [] := List.drop_eq_nil_of_le h
  simp [subList, hd]

/-- When `limit ≤ start`, `subList` returns empty (length truncates to 0 via Nat subtraction). -/

lemma subList_limit_le_start (l : List α) (start limit : Nat) (h : limit ≤ start) :
    subList l start limit = [] := by
  have : limit - start = 0 := Nat.sub_eq_zero_of_le h
  simp [subList, this]

/-- Taking `subList` with `limit = l.length` equals `l.drop start` (when `start ≤ l.length`). -/
lemma subList_limit_eq_length (l : List α) (start : Nat) (h : start ≤ l.length) :
    subList l start l.length = l.drop start := by
  have : (l.drop start).take (l.length - start) = l.drop start := by
    apply List.take_of_length_le
    have : (l.drop start).length = l.length - start := by
      simpa using Nat.sub_add_cancel' h
    omega
  unfold subList
  rw [this]

/-! ### All subarray sums (index-pair direct generation) -/

/-- Generate all contiguous subarray sums of `arr`.
For each `i` from `0` to `n-1` and `j` from `i` to `n-1`,
compute the sum of `arr[i..j]` and collect the results.
This generates sums directly from index pairs without creating intermediate sublists. -/
def allSubarraySums (arr : List α) [AddCommMonoid α] : List α :=
  let n := arr.length
  (List.range n).flatMap (fun i =>
    (List.range' i (n - i)).map (fun j => sliceSum arr i j))

/-- If `i ≤ j < arr.length`, then `sliceSum arr i j` is in `allSubarraySums arr`. -/
lemma allSubarraySums_complete {α} [AddCommMonoid α] (arr : List α) (i j : Nat)
    (hij : i ≤ j) (hj : j < arr.length) : sliceSum arr i j ∈ allSubarraySums arr := by
  have hi : i < arr.length := Nat.lt_of_le_of_lt hij hj
  unfold allSubarraySums
  have hmem_range_i : i ∈ List.range (arr.length) := List.mem_range.mpr hi
  have hmem_range'_j : j ∈ List.range' i (arr.length - i) := by
    rw [List.mem_range']
    refine ⟨j - i, Nat.sub_lt_sub_right hij hj, ?_⟩
    omega
  have hmap : sliceSum arr i j ∈
      (List.range' i (arr.length - i)).map (fun j' => sliceSum arr i j') :=
    List.mem_map.mpr ⟨j, hmem_range'_j, rfl⟩
  exact List.mem_flatMap.mpr ⟨i, hmem_range_i, hmap⟩

/-- If `x ∈ allSubarraySums arr`, then there exist `i ≤ j < arr.length`
such that `x = sliceSum arr i j`. -/
lemma allSubarraySums_sound {α} [AddCommMonoid α] (arr : List α) (x : α)
    (h : x ∈ allSubarraySums arr) : ∃ i j, i ≤ j ∧ j < arr.length ∧ x = sliceSum arr i j := by
  unfold allSubarraySums at h
  rcases List.mem_flatMap.mp h with ⟨i, hi_range, hmap⟩
  rcases List.mem_map.mp hmap with ⟨j, hj_range', hx⟩
  rcases List.mem_range'.mp hj_range' with ⟨k, hk, hj_eq⟩
  have hi : i < arr.length := List.mem_range.mp hi_range
  have hj_lt_len : j < arr.length := by
    have : k < arr.length - i := hk
    omega
  have hle : i ≤ j := by
    omega
  exact ⟨i, j, hle, hj_lt_len, hx.symm⟩

end List

namespace List

/-! ### Sublist helper lemmas -/

/-- If `a :: r` is a sublist of `bs`, then `r` is also a sublist of `bs`. -/
lemma sublist_tail_of_cons_sublist {α : Type} {a : α} {r bs : List α}
    (h : List.Sublist (a :: r) bs) : List.Sublist r bs := by
  have h_tail := h.tail
  simpa using h_tail.trans (List.tail_sublist bs)

/-- If `k ≤ n`, then `List.replicate k a` is a sublist of `List.replicate n a`. -/
lemma replicate_sublist_of_le {α : Type} {a : α} {k n : Nat} (h_le : k ≤ n) :
    (List.replicate k a).Sublist (List.replicate n a) := by
  induction' k with k ih generalizing n
  · exact List.nil_sublist _
  · cases n
    · omega
    · rename_i n
      have hk_le_n : k ≤ n := by omega
      rw [List.replicate_succ, List.replicate_succ]
      exact (ih hk_le_n).cons₂ a

/-- If `P a` holds, then for any `n` there exists a list of length `n` where every element
satisfies `P`. The witness is `List.replicate n a`. This is a clean existence lemma that
packages `List.length_replicate` and `List.mem_replicate` into a single `∃` statement. -/
lemma exists_list_of_length_forall_mem {α : Type} (n : Nat) (a : α) (P : α → Prop) (hP : P a) :
    ∃ (l : List α), l.length = n ∧ (∀ x ∈ l, P x) := by
  refine ⟨List.replicate n a, ?_, ?_⟩
  · simp
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    exact hP

/-- If `A` is a sublist of `nums` and `A ≠ nums`, then `A.length < nums.length`.
This strengthens `List.Sublist.length_le` for the strict case. -/
lemma sublist_length_lt {A nums : List α} (hsub : A.Sublist nums) (hne : A ≠ nums) :
    A.length < nums.length := by
  have hle := List.Sublist.length_le hsub
  have : A.length ≠ nums.length := by
    intro heq
    apply hne
    exact List.Sublist.eq_of_length hsub heq
  omega

/-- Inversion lemma for `Sublist` on a cons: if `l₁ <+ a::l₂`, then either
`l₁ <+ l₂` (skipping `a`) or `l₁ = a::l₁'` with `l₁' <+ l₂` (matching `a`).
This is the forward direction of `List.sublist_cons_iff`, providing direct
case analysis on the `Sublist` relation. Useful in induction proofs over
`Sublist`. -/
lemma sublist_cons_inv {l₁ l₂ : List α} {a : α} (h : l₁ <+ a :: l₂) :
    l₁ <+ l₂ ∨ (∃ l₁', l₁ = a :: l₁' ∧ l₁' <+ l₂) := by
  cases h with
  | cons _ h' => exact Or.inl h'
  | cons₂ _ h' => exact Or.inr ⟨_, rfl, h'⟩

end List


namespace List

/-! # `splitOnP` length and sum lemmas

Lemmas about the relationship between `splitOnP`, `countP`, and list length.
The key insight is that splitting on a predicate `p` partitions the list into
`countP p l + 1` chunks whose lengths sum to `l.length - countP p l`.
-/

/-- `splitOnP.go` never returns an empty list, regardless of the accumulator.
This is the fundamental lemma underlying `splitOnP_ne_nil`: splitting always
produces at least one chunk. -/
lemma splitOnP_go_ne_nil {α : Type u} (p : α → Bool) (l acc : List α) :
    splitOnP.go p l acc ≠ [] := by
  induction l generalizing acc with
  | nil =>
    simp [splitOnP.go]
  | cons a t ih =>
    simp [splitOnP.go]
    split
    · simp
    · apply ih

/-- Core lemma: `(splitOnP.go p l acc).length = countP p l + 1`.
This holds regardless of the accumulator `acc`, which is why the lemma is stated
in terms of `splitOnP.go` rather than `splitOnP`. The accumulator only contributes
to the *content* of the result, not its length (because `splitOnP.go` always
produces the same number of chunks). -/
lemma splitOnP_go_length_eq_countP_add_one {α : Type _} (p : α → Bool) (l acc : List α) :
    (splitOnP.go p l acc).length = countP p l + 1 := by
  induction l generalizing acc with
  | nil =>
    simp [splitOnP.go]
  | cons x xs ih =>
    simp [splitOnP.go]
    by_cases hx : p x = true
    · simp [hx, ih []]
    · simp [hx, ih (x :: acc)]

/-- `(splitOnP p l).length = countP p l + 1`.
This follows directly from `splitOnP_go_length_eq_countP_add_one` since
`splitOnP p l = splitOnP.go p l []`. -/
lemma splitOnP_length_eq_countP_add_one {α : Type _} (p : α → Bool) (l : List α) :
    (splitOnP p l).length = countP p l + 1 := by
  simp [splitOnP, splitOnP_go_length_eq_countP_add_one p l []]

/-- General sum-of-lengths lemma: the total length of the original list equals
the sum of the lengths of the split chunks plus the number of separators
(i.e., `countP p l`). This is a fundamental identity linking `splitOnP` to `countP`.

In other words, `l.length = sum(chunk lengths) + countP p l`. -/
lemma sum_length_splitOnP_add_countP {α : Type _} (p : α → Bool) (l : List α) :
    l.length = ((splitOnP p l).map length).sum + countP p l := by
  induction l with
  | nil =>
    simp [splitOnP_nil, countP_nil]
  | cons x xs ih =>
    rw [splitOnP_cons, countP_cons]
    by_cases hx : p x = true
    · rw [if_pos hx]
      simp [hx]
      rw [ih]
      omega
    · rw [if_neg hx]
      simp [hx]
      have hne : splitOnP p xs ≠ [] := splitOnP_ne_nil p xs
      rcases exists_cons_of_ne_nil hne with ⟨first, rest, hsplit⟩
      rw [hsplit]
      simp [modifyHead]
      rw [hsplit] at ih
      have hsum : ((first :: rest).map length).sum =
          first.length + (rest.map length).sum := by simp
      rw [hsum] at ih
      rw [ih]
      omega

/-! ### Elements of segments do not satisfy the predicate -/

/-- Lemma about `splitOnP.go` with a single-element accumulator: if no element
    of `l` satisfies `P`, then all elements are prepended to the accumulator
    and reversed at the end. -/
lemma splitOnP_go_of_forall_not (P : α → Bool) (l acc : List α)
    (h : ∀ x ∈ l, P x = false) : List.splitOnP.go P l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil => simp [List.splitOnP.go]
  | cons a as ih =>
    have ha : P a = false := h a (by simp)
    have has : ∀ x ∈ as, P x = false := by
      intro x hx; apply h x; simp [hx]
    simp [List.splitOnP.go, ha]
    rw [ih (a :: acc) has]
    simp

/-- If no element of `l` satisfies `P`, then `splitOnP` returns `[l]`. -/
lemma splitOnP_of_forall_not (P : α → Bool) (l : List α) (h : ∀ x ∈ l, P x = false) :
    List.splitOnP P l = [l] := by
  rw [List.splitOnP, splitOnP_go_of_forall_not P l [] h]
  simp

/-- Lemma about `splitOnP.go` when processing a prefix with no `P`-satisfying elements
    followed by a `P`-satisfying element and the rest. -/
lemma splitOnP_go_prefix_sep (P : α → Bool) (l₁ l₂ : List α) (a : α) (acc : List α)
    (h₁ : ∀ x ∈ l₁, P x = false) (ha : P a = true) :
    List.splitOnP.go P (l₁ ++ a :: l₂) acc =
      (acc.reverse ++ l₁) :: List.splitOnP.go P l₂ [] := by
  induction l₁ generalizing acc with
  | nil =>
    simp [List.splitOnP.go, ha]
  | cons x xs ih =>
    have hx : P x = false := h₁ x (by simp)
    have hxs : ∀ y ∈ xs, P y = false := by
      intro y hy; apply h₁ y; simp [hy]
    simp [List.splitOnP.go, hx]
    rw [ih (x :: acc) hxs]
    simp

/-- `splitOnP` of a prefix where `P` is false for all elements, followed by an element
    where `P` is true, followed by the rest. -/
lemma splitOnP_prefix_sep_suffix (P : α → Bool) (l₁ l₂ : List α) (a : α)
    (h₁ : ∀ x ∈ l₁, P x = false) (ha : P a = true) :
    List.splitOnP P (l₁ ++ [a] ++ l₂) = l₁ :: List.splitOnP P l₂ := by
  rw [List.splitOnP, List.splitOnP]
  simp [splitOnP_go_prefix_sep P l₁ l₂ a [] h₁ ha]

/-- Elements of segments produced by `splitOnP.go` do not satisfy `P`. -/
lemma splitOnP_go_elements_not_P (P : α → Bool) (l acc : List α)
    (h_acc : ∀ x ∈ acc, P x = false) :
    ∀ seg ∈ List.splitOnP.go P l acc, ∀ x ∈ seg, P x = false := by
  induction l generalizing acc with
  | nil =>
    rw [List.splitOnP.go]
    intro seg
    simp
    intro h x hx
    subst h
    rw [List.mem_reverse] at hx
    exact h_acc x hx
  | cons a l' ih =>
    by_cases hpa : P a = true
    · rw [List.splitOnP.go, if_pos hpa]
      intro seg
      simp
      rintro (rfl | hseg) x hx
      · rw [List.mem_reverse] at hx
        exact h_acc x hx
      · exact ih [] (fun x hx => by
          exfalso
          exact List.not_mem_nil x hx) seg hseg x hx
    · have hpa_false : P a = false := by
        cases h' : P a
        · rfl
        · exfalso; exact hpa h'
      rw [List.splitOnP.go]
      simp [hpa_false]
      have h_acc' : ∀ x ∈ a :: acc, P x = false := by
        intro x hx
        simp at hx
        rcases hx with (rfl | hx)
        · exact hpa_false
        · exact h_acc x hx
      exact ih (a :: acc) h_acc'

/-- Elements of segments produced by `splitOnP` do not satisfy `P`. -/
lemma splitOnP_elements_not_P (P : α → Bool) (l : List α) :
    ∀ seg ∈ List.splitOnP P l, ∀ x ∈ seg, P x = false := by
  simpa [List.splitOnP] using
    splitOnP_go_elements_not_P P l [] (by intro x hx; exfalso; exact List.not_mem_nil x hx)

end List

namespace List

/-! ### `splitOnP` membership properties -/

/-- If a list `part` is a member of the result of splitting `cs` by predicate `p`,
then no element in `part` satisfies `p`. This is a fundamental property of `splitOnP`:
the splitting predicate `p` is false on every element within a sublist produced by the split. -/
lemma splitOnP_mem_not_p {α : Type*} (p : α → Bool) (cs part : List α)
    (hpart : part ∈ cs.splitOnP p) : ∀ c ∈ part, p c = false := by
  induction' cs with hd tl ih generalizing part
  · have hpart' : part = [] := by
      simpa [splitOnP_nil] using hpart
    subst hpart'; simp
  · rw [splitOnP_cons] at hpart
    split_ifs at hpart with hp
    · simp at hpart
      rcases hpart with (rfl | hmem)
      · simp
      · exact ih part hmem
    · have hne : tl.splitOnP p ≠ [] := splitOnP_ne_nil p tl
      cases hlist : tl.splitOnP p with
      | nil => exact (hne hlist).elim
      | cons xs xss =>
        rw [hlist, modifyHead] at hpart
        simp at hpart
        rcases hpart with (hpart_eq | hmem)
        · subst hpart_eq
          intro c hc
          simp at hc
          rcases hc with (hc_eq | hc_mem)
          · rw [hc_eq]
            cases hp_val : p hd
            · rfl
            · exfalso; exact hp hp_val
          · exact ih xs (by rw [hlist]; simp) c hc_mem
        · intro c hc
          have hmem' : part ∈ tl.splitOnP p := by
            rw [hlist]; exact mem_cons_of_mem xs hmem
          exact ih part hmem' c hc

/-- If a list `part` is a member of the result of splitting `cs` by predicate `p`,
then every element of `part` is also an element of `cs`.
That is, split sublists are always sublists (in the set sense) of the original list. -/
lemma splitOnP_subset {α : Type*} (p : α → Bool) (cs part : List α)
    (hpart : part ∈ cs.splitOnP p) : part ⊆ cs := by
  induction' cs with hd tl ih generalizing part
  · have hpart' : part = [] := by
      simpa [splitOnP_nil] using hpart
    subst hpart'; simp
  · rw [splitOnP_cons] at hpart
    split_ifs at hpart with hp
    · simp at hpart
      rcases hpart with (rfl | hmem)
      · simp
      · intro x hx
        have hx' : x ∈ tl := ih part hmem hx
        simp [hx']
    · have hne : tl.splitOnP p ≠ [] := splitOnP_ne_nil p tl
      cases hlist : tl.splitOnP p with
      | nil => exact (hne hlist).elim
      | cons xs xss =>
        rw [hlist, modifyHead] at hpart
        simp at hpart
        rcases hpart with (hpart_eq | hmem)
        · subst hpart_eq
          intro x hx
          simp at hx
          rcases hx with (hx_eq | hx_mem)
          · rw [hx_eq]; simp
          · have hx' : x ∈ tl := ih xs (by rw [hlist]; simp) hx_mem
            simp [hx']
        · intro x hx
          have hmem' : part ∈ tl.splitOnP p := by
            rw [hlist]; exact mem_cons_of_mem xs hmem
          have hx' : x ∈ tl := ih part hmem' hx
          simp [hx']

end List


namespace List

/-! ### `rdropWhile` — identity when no element satisfies the predicate -/

/-- `rdropWhile p` is the identity when no element of the list satisfies `p`. -/
lemma rdropWhile_eq_self_of_forall_not {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, ¬ p a) : rdropWhile p l = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have ha : ¬ p a := h a (by simp)
    have ha_bool : ¬ p a = true := by simpa using ha
    rw [List.rdropWhile_concat_neg p l a ha_bool]

/-! ### Decomposition by reverse `dropWhile` -/

/-- Decompose a list `l` into the prefix without trailing elements satisfying `p`
    and the suffix of trailing elements satisfying `p` (in original order). -/
lemma reverse_dropWhile_append_decomp {α : Type u} (p : α → Bool) (l : List α) :
    l = (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse := by
  calc
    l = (l.reverse).reverse := by simp
    _ = (l.reverse.takeWhile p ++ l.reverse.dropWhile p).reverse := by
      apply congrArg List.reverse
      exact (takeWhile_append_dropWhile p l.reverse).symm
    _ = (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse := by
      rw [List.reverse_append]

/-! ### `dropTrailing` — drop elements from the end of a list -/

/-- Drop trailing elements satisfying predicate `p` from a list.
Equivalent to reversing, dropping from the front with `dropWhile p`, then reversing back.
For example, `dropTrailing Char.isSpace [' ', 'a', ' '] = [' ', 'a']`. -/
def dropTrailing {α : Type _} (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

/-- `dropTrailing p l` is a prefix of `l` (i.e., `dropTrailing` does not change order
or insert elements). This follows from the decomposition lemma
`reverse_dropWhile_append_decomp`. -/
lemma dropTrailing_prefix (p : α → Bool) (l : List α) : dropTrailing p l <+: l := by
  have h := reverse_dropWhile_append_decomp p l
  -- h: l = (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse
  -- So dropTrailing p l is a prefix of l
  unfold dropTrailing
  have h_eq : (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse = l := by
    simpa using h.symm
  -- show (l.reverse.dropWhile p).reverse <+: l
  have h_prefix : (l.reverse.dropWhile p).reverse <+:
      (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse :=
    List.prefix_append _ _
  rw [h_eq] at h_prefix
  exact h_prefix

end List
