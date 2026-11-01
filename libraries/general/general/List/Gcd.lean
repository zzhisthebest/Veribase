import Mathlib

namespace List

/-! ### GCD of a list of natural numbers -/

/-- GCD of all elements in a list of natural numbers.
Returns `0` for the empty list (since `0` is the identity for `Nat.gcd`). -/
def gcdOfList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.gcd x (gcdOfList xs)


lemma gcdOfList_nil : gcdOfList [] = 0 := rfl


lemma gcdOfList_singleton (x : Nat) : gcdOfList [x] = x := by
  simp [gcdOfList]

lemma gcdOfList_cons (x : Nat) (xs : List Nat) : gcdOfList (x :: xs) = Nat.gcd x (gcdOfList xs) := rfl

/-- The GCD of a list divides each element in the list. -/
lemma gcdOfList_dvd_of_mem (l : List Nat) (d : Nat) (hd : d ∈ l) : gcdOfList l ∣ d := by
  induction' l with a as ih generalizing d
  · exfalso; exact List.not_mem_nil d hd
  · cases hd with
    | head =>
      unfold gcdOfList
      exact Nat.gcd_dvd_left _ _
    | tail _ hd' =>
      have h_gcd : gcdOfList as ∣ d := ih _ hd'
      unfold gcdOfList
      have h_right : Nat.gcd a (gcdOfList as) ∣ gcdOfList as := Nat.gcd_dvd_right _ _
      exact Nat.dvd_trans h_right h_gcd

/-- If `x` divides every element of `l`, then `x` divides `gcdOfList l`. -/
lemma dvd_gcdOfList_of_forall_dvd (l : List Nat) (x : Nat) (h : ∀ d ∈ l, x ∣ d) : x ∣ gcdOfList l := by
  induction' l with a as ih
  · unfold gcdOfList; simp
  · have hx_a : x ∣ a := h a (by simp)
    have hx_as : ∀ d ∈ as, x ∣ d := fun d hd => h d (by simp [hd])
    have ih_as : x ∣ gcdOfList as := ih hx_as
    unfold gcdOfList
    exact Nat.dvd_gcd hx_a ih_as

/-- If every element of `l` is congruent to `0` mod `x`, then `gcdOfList l` is also
congruent to `0` mod `x`. -/
lemma gcdOfList_mod_eq_zero_of_forall_mod_eq_zero (l : List Nat) (x : Nat)
    (h : ∀ d ∈ l, d % x = 0) : (gcdOfList l) % x = 0 := by
  have h_divides : ∀ d ∈ l, x ∣ d := by
    intro d hd
    exact Nat.dvd_of_mod_eq_zero (h d hd)
  have h_divides_gcd : x ∣ gcdOfList l := dvd_gcdOfList_of_forall_dvd l x h_divides
  exact Nat.mod_eq_zero_of_dvd h_divides_gcd

/-- If `gcdOfList l` is congruent to `0` mod `x`, then every element of `l` is congruent
to `0` mod `x`. -/
lemma forall_mod_eq_zero_of_gcdOfList_mod_eq_zero (l : List Nat) (x : Nat)
    (h : (gcdOfList l) % x = 0) : ∀ d ∈ l, d % x = 0 := by
  intro d hd
  have hx_dvd_g : x ∣ gcdOfList l := Nat.dvd_of_mod_eq_zero h
  have hg_dvd_d : gcdOfList l ∣ d := gcdOfList_dvd_of_mem l d hd
  have hx_dvd_d : x ∣ d := Nat.dvd_trans hx_dvd_g hg_dvd_d
  exact Nat.mod_eq_zero_of_dvd hx_dvd_d

/-- `gcdOfList l % x = 0` iff every element of `l` is congruent to `0` mod `x`.
This is the bidirectional version combining the two one-way lemmas. -/
lemma gcdOfList_mod_eq_zero_iff (l : List Nat) (x : Nat) :
    (gcdOfList l) % x = 0 ↔ ∀ d ∈ l, d % x = 0 := by
  constructor
  · exact forall_mod_eq_zero_of_gcdOfList_mod_eq_zero l x
  · exact gcdOfList_mod_eq_zero_of_forall_mod_eq_zero l x

/-! ### `gcdByFoldl` — GCD via `foldl` accumulator -/

/-- GCD of all elements in a list, using `foldl` with initial value `0`.
Since `Nat.gcd 0 a = a`, the initial value `0` acts as the identity for `Nat.gcd`.
This is an alternative to `gcdOfList` using a fold-based accumulator pattern
that is convenient for induction proofs about divisibility.
Both definitions compute the same result: `gcdByFoldl l = gcdOfList l`. -/
def gcdByFoldl (l : List Nat) : Nat := l.foldl Nat.gcd 0


lemma gcdByFoldl_nil : gcdByFoldl [] = 0 := rfl


lemma gcdByFoldl_singleton (x : Nat) : gcdByFoldl [x] = x := by
  simp [gcdByFoldl]

lemma gcdByFoldl_cons (x : Nat) (xs : List Nat) : gcdByFoldl (x :: xs) = xs.foldl Nat.gcd x := by
  simp [gcdByFoldl, List.foldl_cons, Nat.gcd_zero_left]

/-! ### `foldl`-based GCD theorems

These lemmas work with `List.foldl Nat.gcd a` for an arbitrary accumulator `a`,
which is a common pattern in algorithmic proofs. They complement the `gcdOfList`
lemmas but use the foldl accumulator pattern. -/

/-- `foldl Nat.gcd a` divides the initial accumulator `a`. -/
lemma foldl_gcd_divides_init (l : List Nat) (a : Nat) : (l.foldl Nat.gcd a) ∣ a := by
  induction' l with n l ih generalizing a
  · exact dvd_refl a
  · rw [List.foldl_cons]
    have h := ih (Nat.gcd a n)
    exact dvd_trans h (Nat.gcd_dvd_left a n)

/-- `foldl Nat.gcd a` divides every element in the list. -/
lemma foldl_gcd_divides_each (l : List Nat) (a b : Nat) (h : b ∈ l) : (l.foldl Nat.gcd a) ∣ b := by
  induction l generalizing a b with
  | nil => simp at h
  | cons n l ih =>
    rw [List.foldl_cons]
    cases h with
    | head =>
      have hfold := foldl_gcd_divides_init l (Nat.gcd a n)
      exact dvd_trans hfold (Nat.gcd_dvd_right a n)
    | tail _ h' =>
      exact ih (Nat.gcd a n) b h'

/-- If `h` divides the initial accumulator `a` and every `b` in `l`, then `h` divides
`l.foldl Nat.gcd a`. -/
lemma dvd_foldl_gcd (l : List Nat) (a h : Nat) (h_init : h ∣ a) (h_all : ∀ b, b ∈ l → h ∣ b) :
    h ∣ (l.foldl Nat.gcd a) := by
  induction' l with n l ih generalizing a
  · exact h_init
  · rw [List.foldl_cons]
    apply ih (Nat.gcd a n)
    · apply Nat.dvd_gcd h_init (h_all n (by simp))
    · intro b hb
      apply h_all b
      exact List.mem_cons_of_mem n hb

/-- If `a > 0`, then `l.foldl Nat.gcd a` stays positive, regardless of `l`. -/
lemma foldl_gcd_pos (l : List Nat) (a : Nat) (ha : a > 0) : (l.foldl Nat.gcd a) > 0 := by
  induction' l with n l ih generalizing a
  · exact ha
  · rw [List.foldl_cons]
    apply ih (Nat.gcd a n)
    by_contra! hz
    have hz_eq : Nat.gcd a n = 0 := by omega
    rcases Nat.gcd_eq_zero_iff.mp hz_eq with ⟨ha0, hn0⟩
    omega

/-- If a nonempty list of positive integers has a common divisor `x > 1`,
then `gcdOfList l > 1`. -/
lemma gcdOfList_gt_one_of_exists_gt_one_dvd_all {l : List Nat} (h_ne : l ≠ [])
    (h_pos : ∀ a ∈ l, a > 0) (x : Nat) (hx_gt_one : x > 1)
    (hx_dvd_all : ∀ a ∈ l, x ∣ a) : gcdOfList l > 1 := by
  have hx_dvd_gcd : x ∣ gcdOfList l := dvd_gcdOfList_of_forall_dvd l x hx_dvd_all
  cases l with
  | nil => exact absurd rfl h_ne
  | cons hd tl =>
    have h_hd_pos : hd > 0 := h_pos hd (by simp)
    have h_gcd_dvd_hd : gcdOfList (hd :: tl) ∣ hd := gcdOfList_dvd_of_mem (hd :: tl) hd (by simp)
    have h_gcd_pos : gcdOfList (hd :: tl) > 0 := Nat.pos_of_dvd_of_pos h_gcd_dvd_hd h_hd_pos
    have hx_le_gcd : x ≤ gcdOfList (hd :: tl) := Nat.le_of_dvd h_gcd_pos hx_dvd_gcd
    omega

/-- `gcdByFoldl` equals `gcdOfList` — both compute the same GCD of a list.
Proved via mutual divisibility using the foldl/gcd divisibility lemmas. -/
lemma gcdByFoldl_eq_gcdOfList (l : List Nat) : gcdByFoldl l = gcdOfList l := by
  apply Nat.dvd_antisymm
  · -- gcdByFoldl l ∣ gcdOfList l
    apply dvd_gcdOfList_of_forall_dvd l (gcdByFoldl l)
    intro d hd
    have h_gcdByFoldl : gcdByFoldl l = l.foldl Nat.gcd 0 := rfl
    rw [h_gcdByFoldl]
    exact foldl_gcd_divides_each l 0 d hd
  · -- gcdOfList l ∣ gcdByFoldl l
    rw [show gcdByFoldl l = l.foldl Nat.gcd 0 from rfl]
    apply dvd_foldl_gcd l 0 (gcdOfList l)
    · exact dvd_zero _
    · intro b hb
      exact gcdOfList_dvd_of_mem l b hb

/-! ### LCM of a list of natural numbers -/

/-- LCM of a list of natural numbers; the LCM of the empty list is 1 (the identity for `Nat.lcm`). -/
def lcmOfList : List Nat → Nat
| []      => 1
| x :: xs => Nat.lcm x (lcmOfList xs)


lemma lcmOfList_nil : lcmOfList [] = 1 := rfl


lemma lcmOfList_singleton (x : Nat) : lcmOfList [x] = x := by
  simp [lcmOfList]

lemma lcmOfList_cons (x : Nat) (xs : List Nat) : lcmOfList (x :: xs) = Nat.lcm x (lcmOfList xs) := rfl

/-! ### `lcmByFoldl` — LCM via `foldl` accumulator -/

/-- LCM of all elements in a list, using `foldl` with initial value `1`.
Since `Nat.lcm 1 a = a`, the initial value `1` acts as the identity for `Nat.lcm`.
This is a fold-based accumulator version of `lcmOfList`, symmetric to `gcdByFoldl`. -/
def lcmByFoldl (l : List Nat) : Nat := l.foldl Nat.lcm 1


lemma lcmByFoldl_nil : lcmByFoldl [] = 1 := rfl


lemma lcmByFoldl_singleton (x : Nat) : lcmByFoldl [x] = x := by
  simp [lcmByFoldl]

lemma lcmByFoldl_cons (x : Nat) (xs : List Nat) : lcmByFoldl (x :: xs) = xs.foldl Nat.lcm x := by
  simp [lcmByFoldl, List.foldl_cons, Nat.lcm_one_left]

/-- A foldl-based formulation: `l.foldl Nat.lcm a` equals `Nat.lcm a (l.foldl Nat.lcm 1)`.
This is the key identity that relates folding with a custom initial accumulator `a`
to folding with the identity `1`. -/
lemma foldl_lcm_eq_lcm_foldl_one (l : List Nat) (a : Nat) : l.foldl Nat.lcm a = Nat.lcm a (l.foldl Nat.lcm 1) := by
  induction' l with b bs ih generalizing a
  · simp
  · rw [List.foldl_cons, List.foldl_cons, Nat.lcm_one_left]
    rw [ih (Nat.lcm a b), Nat.lcm_assoc, ← ih b]

/-- `lcmByFoldl` equals `lcmOfList` — both compute the same LCM of a list. -/
lemma lcmByFoldl_eq_lcmOfList (l : List Nat) : lcmByFoldl l = lcmOfList l := by
  induction' l with a as ih
  · rfl
  · rw [lcmByFoldl_cons, lcmOfList_cons]
    rw [foldl_lcm_eq_lcm_foldl_one, ← ih]
    rfl

/-! ### Generic GCDMonoid foldl-based GCD and LCM

These generalize `gcdByFoldl` and `lcmByFoldl` from `Nat` to any `GCDMonoid`. -/

/-- Foldl gcd over a list in any GCD monoid. Identity is 0.
This is the generic version of `gcdByFoldl` that works for any `GCDMonoid` type,
not just `Nat`. The initial value `0` acts as the identity for `gcd`. -/
def gcdList {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (l : List α) : α :=
  l.foldl gcd 0


lemma gcdList_nil [CancelCommMonoidWithZero α] [GCDMonoid α] : gcdList ([] : List α) = (0 : α) := rfl

/-- Foldl lcm over a list in any GCD monoid. Identity is 1.
This is the generic version of `lcmByFoldl` that works for any `GCDMonoid` type,
not just `Nat`. The initial value `1` acts as the identity for `lcm`. -/
def lcmList {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (l : List α) : α :=
  l.foldl lcm 1


lemma lcmList_nil [CancelCommMonoidWithZero α] [GCDMonoid α] : lcmList ([] : List α) = (1 : α) := rfl

/-! ### `gcd_foldl` — parameterized foldl GCD over any GCDMonoid

This section generalizes the foldl-based GCD theorems from `Nat` to any `GCDMonoid`,
with an arbitrary initial accumulator value `init` (not just `0`). -/

/-- Fold gcd over a list, starting from an initial value `init`.
General over any GCDMonoid. This is a parameterized version of `gcdList`
where the initial accumulator can be any value, not just `0`. -/
def gcd_foldl {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (init : α) : List α → α :=
  List.foldl gcd init

/-- `gcd_foldl init xs` divides the initial accumulator `init`. -/
lemma gcd_foldl_dvd_init {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (init : α) (xs : List α) :
    gcd_foldl init xs ∣ init := by
  induction' xs with y ys ih generalizing init
  · simp [gcd_foldl]
  · have h_gcd_dvd : gcd init y ∣ init := gcd_dvd_left init y
    simpa [gcd_foldl] using dvd_trans (ih (gcd init y)) h_gcd_dvd

/-- If `a` is in `xs`, then `gcd_foldl init xs` divides `a`. -/
lemma gcd_foldl_dvd_mem {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (init : α) (xs : List α) (a : α)
    (h : a ∈ xs) : gcd_foldl init xs ∣ a := by
  induction' xs with y ys ih generalizing init
  · exact False.elim (by cases h)
  · rw [List.mem_cons] at h
    cases' h with h_eq h_mem
    · subst h_eq
      simpa [gcd_foldl] using dvd_trans (gcd_foldl_dvd_init (gcd init a) ys) (gcd_dvd_right init a)
    · simpa [gcd_foldl] using ih (gcd init y) h_mem

/-- If `d` divides `init` and every element of `xs`, then `d` divides `gcd_foldl init xs`. -/
lemma dvd_gcd_foldl_of_forall {α : Type} [CancelCommMonoidWithZero α] [GCDMonoid α] (init : α) (xs : List α)
    (d : α) (hd_init : d ∣ init) (hd_all : ∀ a, a ∈ xs → d ∣ a) : d ∣ gcd_foldl init xs := by
  induction' xs with y ys ih generalizing init
  · simpa [gcd_foldl] using hd_init
  · have hy_dvd : d ∣ y := hd_all y (by simp)
    have h_gcd_dvd : d ∣ gcd init y := dvd_gcd hd_init hy_dvd
    have h_rest : ∀ a, a ∈ ys → d ∣ a := λ a ha => hd_all a (by simp [ha])
    simpa [gcd_foldl] using ih (gcd init y) h_gcd_dvd h_rest

end List

namespace List


/-! ### GCD of all elements -/

/-- Compute the GCD of all elements in a list using `Nat.gcd` with `foldl`.
The GCD of an empty list is 0 (since `Nat.gcd 0 n = n`, this gives the identity value).
This is the list counterpart of `Array.gcd`. -/
def gcd (l : List Nat) : Nat :=
  l.foldl Nat.gcd 0

lemma gcd_nil : gcd ([] : List Nat) = 0 := rfl

lemma gcd_singleton (x : Nat) : gcd [x] = x := by
  simp [gcd]

lemma gcd_cons (x : Nat) (xs : List Nat) :
    gcd (x :: xs) = List.foldl Nat.gcd x xs := by
  simp [gcd]


/-! ### `foldlGcd` — GCD of all elements via foldl -/

/-- `foldlGcd l` computes the GCD of all elements in `l` via `foldl gcd 0`.
Since `gcd 0 x = x`, starting from `0` is correct. -/
def foldlGcd (l : List Nat) : Nat :=
  l.foldl Nat.gcd 0


end List

