import Loom.MonadAlgebras.NonDetT.Findable

/-!
# `findNat` theorems

Theorems about `findNat : (Nat → Prop) → [DecidablePred p] → Option Nat`
from `Loom.MonadAlgebras.NonDetT.Findable`, which finds the smallest natural
number satisfying a decidable predicate.
-/

/-- `exists_findNat`: `findNat p` returns `some` iff there exists `x` such that `p x`. -/
lemma exists_findNat (p : Nat → Prop) [DecidablePred p] :
    (∃ x, p x) ↔ (findNat p).isSome := by
  constructor
  · rintro ⟨x, px⟩
    apply AccFrom_findNat; apply AccFrom_of_p <;> aesop
  · simp only [Option.isSome_iff_exists, forall_exists_index]; intro i eq; exists i; revert eq
    unfold findNat; generalize 0 = m;
    apply findNat.aux.partial_correctness; aesop

/-- `findNat_aux_some_le`: if `findNat.aux p i = some j`, then no `k` in `[i, j)` satisfies `p`. -/
lemma findNat_aux_some_le (p : Nat → Prop) [DecidablePred p] (i : Nat) :
    findNat.aux p i = some j → ∀ k, i ≤ k → k < j → ¬ p k := by
  apply findNat.aux.partial_correctness
  intro aux ih i r; split
  · rintro ⟨⟩ ph; omega
  · intro h; have := ih _ _ h
    intros k _ _ pk; apply this k <;> try omega
    by_cases h : k = i; aesop; omega

/-- If `findNat p = some i`, then `p i` holds. -/
lemma findNat_some_p (p : Nat → Prop) [DecidablePred p] (i : Nat) :
    findNat p = some i → p i := by
  simp [findNat]; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

/-- If `p i` holds, then `findNat p` returns `some`. -/
lemma findNat_isSome_of_p (p : Nat → Prop) [DecidablePred p] (i : Nat) (h : p i) :
    (findNat p).isSome :=
  ((exists_findNat p).mp ⟨i, h⟩)

/-- If `findNat p` returns `some i`, then no `k < i` satisfies `p`.
    i.e. `i` is the *first* `Nat` where `p` holds. -/
lemma findNat_some_no_lt (p : Nat → Prop) [DecidablePred p] (i : Nat) (h : findNat p = some i) :
    ∀ k < i, ¬ p k := by
  have h_aux : findNat.aux p 0 = some i := h
  intro k hlt
  exact findNat_aux_some_le p 0 h_aux k (Nat.zero_le _) hlt

/-- If `findNat p` returns `some j`, then `j` is the minimal index
    where `p` holds: for any `i` with `p i`, we have `j ≤ i`. -/
lemma findNat_some_is_min (p : Nat → Prop) [DecidablePred p] {i j : Nat}
    (hj : findNat p = some j) (hpi : p i) : j ≤ i := by
  by_contra! hgt
  exact findNat_some_no_lt p j hj i hgt hpi

/-- If `p i` holds, there exists `j` with `p j`, `j ≤ i`, and `findNat p = some j`. -/
lemma findNat_some_exists_le_of_p (p : Nat → Prop) [DecidablePred p] (i : Nat) (h : p i) :
    ∃ j, p j ∧ j ≤ i ∧ findNat p = some j := by
  have hsome : (findNat p).isSome := findNat_isSome_of_p p i h
  rcases Option.isSome_iff_exists.mp hsome with ⟨j, hj⟩
  have hpj : p j := findNat_some_p p _ hj
  have hle : j ≤ i := findNat_some_is_min p hj h
  exact ⟨j, hpj, hle, hj⟩
