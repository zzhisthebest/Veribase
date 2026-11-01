import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Specific

open _root_.List

namespace List

/-! ## `suffixOfLength`: Take the suffix of a list of a given length

`suffixOfLength xs n` takes the last `min n xs.length` elements of `xs`.
It is equivalent to `xs.drop (xs.length - n)`. For example,
`suffixOfLength [a, b, c, d, e] 3 = [c, d, e]`. -/

/-- Take the suffix of `xs` of length `min n xs.length`.
This drops the first `xs.length - n` elements, keeping the rest. -/
def suffixOfLength (xs : List α) (n : Nat) : List α :=
  xs.drop (xs.length - n)

/-- The length of `suffixOfLength xs n` is `min n xs.length`. -/
theorem length_suffixOfLength (xs : List α) (n : Nat) :
    (suffixOfLength xs n).length = min n xs.length := by
  rw [suffixOfLength, List.length_drop]
  omega

/-- Every element of `suffixOfLength xs n` is also an element of `xs`. -/
theorem suffixOfLength_subset (xs : List α) (n : Nat) :
    ∀ x ∈ suffixOfLength xs n, x ∈ xs := by
  intro x hx
  exact List.mem_of_mem_drop hx

/-- `suffixOfLength` can be expressed as dropping the prefix
whose length is the difference between the original length and the suffix length. -/
theorem suffixOfLength_eq_drop_length_sub_length (xs : List α) (n : Nat) :
    suffixOfLength xs n = xs.drop (xs.length - (suffixOfLength xs n).length) := by
  unfold suffixOfLength
  rw [List.length_drop]
  congr 1
  omega

/-- If the list is shorter than the requested length, `suffixOfLength` returns
the entire list unchanged. -/
theorem suffixOfLength_eq_self_of_length_le {xs : List α} {n : Nat} (h : xs.length ≤ n) :
    suffixOfLength xs n = xs := by
  unfold suffixOfLength
  have hdrop : xs.length - n = 0 := by
    omega
  rw [hdrop]
  rfl

/-! ## `filteredSuffix`: Suffix of a filtered list

`filteredSuffix p xs n` first filters `xs` by predicate `p`, then takes
a suffix of the result of length (at most) `n`. -/

/-- Filter `xs` by `p`, then take a suffix of length `min n (filtered length)`. -/
def filteredSuffix (p : α → Prop) [DecidablePred p] (xs : List α) (n : Nat) : List α :=
  suffixOfLength (xs.filter p) n

/-- The length of `filteredSuffix p xs n` is `min n (xs.filter p).length`. -/
theorem length_filteredSuffix (p : α → Prop) [DecidablePred p] (xs : List α) (n : Nat) :
    (filteredSuffix p xs n).length = min n (xs.filter p).length := by
  simp [filteredSuffix, length_suffixOfLength]

/-- Every element of `filteredSuffix p xs n` satisfies `p`. -/
theorem filteredSuffix_property (p : α → Prop) [DecidablePred p] (xs : List α) (n : Nat) :
    ∀ x ∈ filteredSuffix p xs n, p x := by
  intro x hx
  have hSuffix : x ∈ suffixOfLength (xs.filter p) n := by
    simpa [filteredSuffix] using hx
  exact of_decide_eq_true (List.mem_filter.mp (suffixOfLength_subset (xs.filter p) n x hSuffix)).2

/-- Every element of `filteredSuffix p xs n` is also an element of `xs`. -/
theorem filteredSuffix_subset (p : α → Prop) [DecidablePred p] (xs : List α) (n : Nat) :
    ∀ x ∈ filteredSuffix p xs n, x ∈ xs := by
  intro x hx
  have hSuffix : x ∈ suffixOfLength (xs.filter p) n := by
    simpa [filteredSuffix] using hx
  exact (List.mem_filter.mp (suffixOfLength_subset (xs.filter p) n x hSuffix)).1

/-- `filteredSuffix` can be expressed as dropping a prefix of the filtered list. -/
theorem filteredSuffix_eq_filter_drop_length_sub_length
    (p : α → Prop) [DecidablePred p] (xs : List α) (n : Nat) :
    filteredSuffix p xs n =
      (xs.filter p).drop ((xs.filter p).length - (filteredSuffix p xs n).length) := by
  simpa [filteredSuffix] using suffixOfLength_eq_drop_length_sub_length (xs.filter p) n

/-- If the filtered list's length is at most `n`, then `filteredSuffix` returns
the entire filtered list. -/
theorem filteredSuffix_eq_filter_of_filter_length_le
    (p : α → Prop) [DecidablePred p] {xs : List α} {n : Nat}
    (h : (xs.filter p).length ≤ n) :
    filteredSuffix p xs n = xs.filter p := by
  exact suffixOfLength_eq_self_of_length_le h

/-- If the original list's length is less than `n`, then `filteredSuffix p xs n`
returns the entire filtered list. -/
theorem filteredSuffix_eq_filter_of_list_length_lt
    (p : α → Prop) [DecidablePred p] {xs : List α} {n : Nat}
    (h : xs.length < n) :
    filteredSuffix p xs n = xs.filter p := by
  apply filteredSuffix_eq_filter_of_filter_length_le
  have hfilter : (xs.filter p).length ≤ xs.length :=
    List.length_filter_le (fun x => decide (p x)) xs
  omega

end List

end Specific
