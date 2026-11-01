import general.List.Permutations

namespace List


/-! ### Palindrome check -/

/-- Check whether a list is a palindrome by comparing it to its reverse. -/
def isPalindrome [DecidableEq α] (l : List α) : Bool :=
  l = l.reverse

/-- `isPalindrome l` is `true` iff `l` equals its reverse. -/

lemma isPalindrome_eq_true_iff [DecidableEq α] (l : List α) : isPalindrome l = true ↔ l = l.reverse := by
  simp [isPalindrome]

/-- `isPalindrome l` is `false` iff `l` differs from its reverse. -/
lemma isPalindrome_eq_false_iff [DecidableEq α] (l : List α) : isPalindrome l = false ↔ l ≠ l.reverse := by
  simp [isPalindrome]

/-! ### `BEq` reverse equality -/

/-- Under `LawfulBEq α`, `(xs.reverse == xs) = true` holds iff `xs` equals its own reverse.
This bridges the `Bool`-valued `BEq` equality test with structural `=` equality,
a common pattern when reasoning about palindrome-like properties with `==`.
For example, this lemma is used to relate `(clean word).reverse == clean word`
to `(clean word).reverse = clean word` in palindrome checking with preprocessed strings. -/
lemma reverse_beq_self_iff {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    (xs.reverse == xs) = true ↔ xs.reverse = xs := by
  simp

/-- The empty list is a palindrome. -/

lemma isPalindrome_nil [DecidableEq α] : isPalindrome ([] : List α) := by
  unfold isPalindrome; rfl

/-- A singleton list is a palindrome. -/

lemma isPalindrome_singleton [DecidableEq α] (a : α) : isPalindrome [a] := by
  unfold isPalindrome; simp

/-- A list concatenated with its reverse is always a palindrome. -/

lemma isPalindrome_append_reverse [DecidableEq α] (l : List α) : isPalindrome (l ++ l.reverse) := by
  unfold isPalindrome; simp

/-- Reversing a list preserves the palindrome property. -/
lemma isPalindrome_reverse [DecidableEq α] (l : List α) : isPalindrome l.reverse = isPalindrome l := by
  simp [isPalindrome, eq_comm]

/-- If `b` is a palindrome (i.e. `b = b.reverse`), then `a ++ b ++ a.reverse` is also
its own reverse. In other words, surrounding a palindrome by a list and its reverse
yields another palindrome. -/
lemma reverse_pal_append {α : Type u} (a b : List α) (hpal : b = b.reverse) :
    (a ++ b ++ a.reverse).reverse = a ++ b ++ a.reverse := by
  calc
    (a ++ b ++ a.reverse).reverse
        = (b ++ a.reverse).reverse ++ a.reverse := by simp
    _ = ((a.reverse).reverse ++ b.reverse) ++ a.reverse := by rw [List.reverse_append]
    _ = (a ++ b.reverse) ++ a.reverse := by simp
    _ = a ++ (b.reverse ++ a.reverse) := by simp
    _ = a ++ (b ++ a.reverse) := by rw [← hpal]
    _ = a ++ b ++ a.reverse := by simp

/-- If `b` is a palindrome, then `a ++ b ++ a.reverse` is also a palindrome. -/
lemma isPalindrome_append_append_reverse [DecidableEq α] (a b : List α)
    (hpal : isPalindrome b = true) : isPalindrome (a ++ b ++ a.reverse) := by
  have h_eq : b = b.reverse := by
    simpa [isPalindrome] using hpal
  simpa [isPalindrome] using (reverse_pal_append a b h_eq).symm

/-! ### Palindrome structural decomposition -/

/-- If a list is a palindrome of length at least 2, it can be decomposed as
`a :: q ++ [a]` for some element `a` and list `q`. This is the fundamental
structural lemma for palindromes of non-trivial length: the first and last
elements must be equal, and the interior is `q`. -/
lemma palindrome_split {α : Type} [DecidableEq α] {l : List α} (hpal : l = l.reverse) (h2 : 2 ≤ l.length) :
    ∃ a q, l = a :: q ++ [a] := by
  cases' l with a l'
  · have hlen : ([] : List α).length = 0 := by simp
    rw [hlen] at h2; omega
  · have h_eq : a :: l' = l'.reverse ++ [a] := by
      simpa [List.reverse_cons] using hpal
    have hl'_ne : l' ≠ [] := by
      intro h
      rw [h] at h_eq
      have : (a :: []).length = 1 := by simp
      have : 2 ≤ 1 := by simpa [h] using h2
      omega
    have hl'rev_ne : l'.reverse ≠ [] := by
      intro h
      apply hl'_ne
      have hlen' : l'.length = 0 := by
        have hlen := congrArg List.length h
        simpa [List.length_reverse] using hlen
      exact List.length_eq_zero_iff.mp hlen'
    have h_tail_eq : l' = l'.reverse.tail ++ [a] := by
      have := congrArg List.tail h_eq
      simpa [hl'rev_ne] using this
    have h_construct : a :: l' = a :: l'.reverse.tail ++ [a] := by
      calc
        a :: l' = a :: (l'.reverse.tail ++ [a]) := congrArg (λ t => a :: t) h_tail_eq
        _ = (a :: l'.reverse.tail) ++ [a] := by rw [List.cons_append]
    refine ⟨a, l'.reverse.tail, h_construct⟩

/-- If a list is a palindrome of length at least 2, its decomposition `l = a :: q ++ [a]`
has the property that `q` is also a palindrome (`q = q.reverse`).
This is a stronger version of `palindrome_split` that additionally gives the
palindromic nature of the interior. -/
lemma palindrome_cons_eq {α : Type} [DecidableEq α] {l : List α} (hpal : l = l.reverse) (h2 : 2 ≤ l.length) :
    ∃ a q, l = a :: q ++ [a] ∧ q = q.reverse := by
  rcases palindrome_split hpal h2 with ⟨a, q, hl_eq⟩
  refine ⟨a, q, hl_eq, ?_⟩
  rw [hl_eq] at hpal
  have h_eq' : a :: q ++ [a] = a :: q.reverse ++ [a] := by
    simpa [List.reverse_cons, List.reverse_append] using hpal
  have h_tail : q ++ [a] = q.reverse ++ [a] := by
    simpa using congrArg List.tail h_eq'
  have h_rev_tail : q.reverse = q := by
    have h_rev : (q ++ [a]).reverse = (q.reverse ++ [a]).reverse := by rw [h_tail]
    rw [List.reverse_append, List.reverse_append, List.reverse_reverse] at h_rev
    have h := congrArg List.tail h_rev
    simpa using h
  rw [h_rev_tail]

/-! ### Character predicates on lists -/

/-- Check whether every `Char` in the list is uppercase (Unicode).
This is the `List Char` counterpart of `String.isAllUpper`. -/
def allUpper (l : List Char) : Bool :=
  l.all Char.isUpper

/-- Check whether every `Char` in the list is lowercase (Unicode).
This is the `List Char` counterpart of `String.isAllLower`. -/
def allLower (l : List Char) : Bool :=
  l.all Char.isLower


end List
