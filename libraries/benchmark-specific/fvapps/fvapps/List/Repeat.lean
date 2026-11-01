import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Repeating and duplicating list elements -/

/-- Repeat each element of `xs` `n` times. -/
def repeatEach {α : Type u} (n : Nat) (xs : List α) : List α :=
  List.flatMap (fun x => List.replicate n x) xs

/-- The length of `repeatEach n xs` is `xs.length * n`. -/
theorem length_repeatEach {α : Type u} (n : Nat) (xs : List α) :
    (repeatEach n xs).length = xs.length * n := by
  induction xs with
  | nil => simp [repeatEach]
  | cons x xs ih =>
      calc
        (repeatEach n (x :: xs)).length = n + (repeatEach n xs).length := by
          simp [repeatEach]
        _ = n + xs.length * n := by rw [ih]
        _ = (x :: xs).length * n := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- Duplicate each element of `xs` (same as `repeatEach 2 xs`). -/
def duplicateEach {α : Type u} (xs : List α) : List α :=
  repeatEach 2 xs

/-- The length of `duplicateEach xs` is `xs.length * 2`. -/
theorem length_duplicateEach {α : Type u} (xs : List α) :
    (duplicateEach xs).length = xs.length * 2 := by
  simpa [duplicateEach] using length_repeatEach (α := α) 2 xs

/-! ## Equality to `replicate` -/

/-- If every element of `l` equals `a`, then `l` is `replicate (length l) a`. -/
lemma eq_replicate_of_forall_eq {α : Type u} (l : List α) (a : α)
    (h : ∀ x ∈ l, x = a) : l = List.replicate l.length a :=
  List.eq_replicate_iff.mpr ⟨rfl, h⟩

/-- If every element of `l` equals `a` and `l` has length `n`, then `l` is `replicate n a`. -/
lemma eq_replicate_of_length_and_forall_eq {α : Type u} (l : List α) (a : α)
    {n : Nat} (hlen : l.length = n) (h : ∀ x ∈ l, x = a) :
    l = List.replicate n a := by
  simpa [hlen] using eq_replicate_of_forall_eq l a h

/-- If `xs.all (· = a)` is true, then `xs` equals `List.replicate xs.length a`.
This provides a `Bool`-valued hypothesis form of `eq_replicate_of_forall_eq`. -/
theorem all_eq_replicate {α : Type u} [DecidableEq α] {xs : List α} {a : α}
    (h : xs.all (· = a) = true) : xs = List.replicate xs.length a :=
  eq_replicate_of_forall_eq xs a (by
    have hall := List.all_eq_true.mp h
    intro x hx
    exact of_decide_eq_true (hall x hx))

/-! ## Mapping a constant value -/

/-- `mapConst a xs` returns a list of `β` with the same length as `xs`,
where every element is `a`. Equivalent to `xs.map (fun _ => a)`. -/
def mapConst {α β : Type u} (a : β) (xs : List α) : List β :=
  xs.map (fun _ => a)

/-- The length of `mapConst a xs` equals the length of `xs`. -/
@[simp]
theorem length_mapConst {α β : Type u} (a : β) (xs : List α) :
    (mapConst a xs).length = xs.length := by
  simp [mapConst]

/-- If `i` is in bounds for `mapConst value xs`, then `getElem?` returns `some value`. -/
theorem getElem?_mapConst {α β : Type} (xs : List α) (value : β) {i : Nat}
    (hi : i < (mapConst value xs).length) :
    (mapConst value xs)[i]? = some value := by
  unfold mapConst
  have hiXs : i < xs.length := by
    simpa [List.length_map] using hi
  rw [List.getElem?_map]
  rw [List.getElem?_eq_getElem hiXs]
  simp

/-- If `i` is in bounds for `mapConst value xs`, then `getElem!` returns `value`. -/
theorem getElem!_mapConst {α β : Type} [Inhabited β] (xs : List α) (value : β) {i : Nat}
    (hi : i < (mapConst value xs).length) :
    (mapConst value xs)[i]! = value := by
  rw [LawfulGetElem.getElem!_def, getElem?_mapConst xs value hi]

/-- If `p value` holds, then `p` holds for every element of `mapConst value xs`. -/
theorem all_mem_mapConst {α β : Type} {xs : List α} {value : β} {p : β → Prop}
    (hvalue : p value) :
    ∀ seen ∈ mapConst value xs, p seen := by
  intro seen hseen
  unfold mapConst at hseen
  rcases List.mem_map.mp hseen with ⟨x, hx, h⟩
  have : value = seen := by simpa using h
  rcases this with rfl
  exact hvalue

/-! ## `repeatFor`: replicate a value for each element -/

/-- `repeatFor a xs` returns a list of `β` with the same length as `xs`, where every element
is `a`. This is implemented via `List.replicate xs.length a`, making membership and count
lemmas readily available via `List.mem_replicate` etc. Equivalent to `mapConst a xs`. -/
def repeatFor {α β : Type u} (a : β) (xs : List α) : List β :=
  List.replicate xs.length a

@[simp]
theorem repeatFor_nil {α β : Type u} (a : β) :
    repeatFor a ([] : List α) = [] := by
  simp [repeatFor]

@[simp]
theorem length_repeatFor {α β : Type u} (a : β) (xs : List α) :
    (repeatFor a xs).length = xs.length := by
  simp [repeatFor]

/-! ## Deduplication of `replicate` lists -/

/-- Helper lemma: deduplicating a list of `n` copies of `x` with initial accumulator `[x]`
yields a list of length at most 2. Used to prove `eraseDups_replicate_length_le_two`. -/
theorem eraseDups_loop_replicate_single_length_le_two {α : Type} [BEq α] [LawfulBEq α] (x : α)
    (n : Nat) :
    (List.eraseDups.loop (List.replicate n x) [x]).length ≤ 2 := by
  induction n with
  | zero =>
      simp [List.eraseDups.loop]
  | succ n ih =>
      simp [List.replicate, List.eraseDups.loop, List.elem, ih]

/-- Removing duplicates from a list of `n` identical copies of `x` yields a list
of length at most 2 (in fact at most 1, but the ≤ 2 bound is sufficient for many
applications and has a simpler proof). -/
theorem eraseDups_replicate_length_le_two {α : Type} [BEq α] [LawfulBEq α] (x : α)
    (n : Nat) :
    (List.eraseDups (List.replicate n x)).length ≤ 2 := by
  cases n with
  | zero =>
      simp [List.eraseDups, List.eraseDups.loop]
  | succ n =>
      simp [List.eraseDups, List.eraseDups.loop, List.replicate, List.elem,
        eraseDups_loop_replicate_single_length_le_two]

/-! ## `repeatOption`: Option-based list creation -/

/-- `repeatOption count opt` returns a list: `List.replicate count value` if `opt = some value`,
or `[]` if `opt = none`. -/
def repeatOption {α : Type u} (count : Nat) : Option α → List α
  | none => []
  | some value => List.replicate count value

/-- The length of `repeatOption count (some value)` is `count`. -/
theorem length_repeatOption_some {α : Type u} (count : Nat) (value : α) :
    List.length (repeatOption count (some value)) = count := by
  simp [repeatOption]

/-- If `x` is in `repeatOption count (some value)`, then `x` equals `value`. -/
theorem mem_repeatOption_some {α : Type u} {count : Nat} {value x : α}
    (h : x ∈ repeatOption count (some value)) :
    x = value := by
  have hx : count ≠ 0 ∧ x = value := by
    simpa [repeatOption] using h
  exact hx.2

/-! ## `separatedReplicate`: two replicate blocks with a separator -/

/-- Creates a list with `i` copies of `fill`, then `sep`, then `j` copies of `fill`.
`separatedReplicate 'x' '/' 3 2` = `['x','x','x','/','x','x']`. -/
def separatedReplicate {α : Type u} (fill sep : α) (i j : Nat) : List α :=
  List.replicate i fill ++ sep :: List.replicate j fill

/-- The length of `separatedReplicate fill sep i j` is `i + 1 + j`. -/
@[simp]
theorem length_separatedReplicate {α : Type u} (fill sep : α) (i j : Nat) :
    (separatedReplicate fill sep i j).length = i + 1 + j := by
  simp [separatedReplicate]
  omega

/-! ## `replicatePair`: two replicate blocks concatenated -/

/-- Creates a list with `leftCount` copies of `leftValue` followed by
`rightCount` copies of `rightValue`.
`replicatePair 3 2 'a' 'b'` = `['a','a','a','b','b']`. -/
def replicatePair {α : Type u} (leftCount rightCount : Nat)
    (leftValue rightValue : α) : List α :=
  List.replicate leftCount leftValue ++ List.replicate rightCount rightValue

/-- The length of `replicatePair leftCount rightCount leftValue rightValue` is
`leftCount + rightCount`. -/
@[simp]
theorem length_replicatePair {α : Type u} (leftCount rightCount : Nat)
    (leftValue rightValue : α) :
    (replicatePair leftCount rightCount leftValue rightValue).length =
      leftCount + rightCount := by
  simp [replicatePair]

/-- If `x` is in a `replicatePair`, then `x` equals either `leftValue` or `rightValue`. -/
theorem mem_replicatePair {α : Type u}
    {x leftValue rightValue : α} {leftCount rightCount : Nat}
    (hx : x ∈ replicatePair leftCount rightCount leftValue rightValue) :
    x = leftValue ∨ x = rightValue := by
  simp [replicatePair, List.mem_append] at hx
  rcases hx with hx | hx
  · exact Or.inl hx.2
  · exact Or.inr hx.2

/-! ## Self-membership of replicated lists -/

/-- If `0 < n`, then `x` is a member of `replicate n x`. This is a direct consequence
of `List.mem_replicate`. -/
theorem mem_replicate_self_of_pos {α : Type u} (x : α) {n : Nat} (hn : 0 < n) :
    x ∈ List.replicate n x := by
  exact List.mem_replicate.mpr ⟨by omega, rfl⟩

/-- If `0 < n`, then `x ∈ base ++ replicate n x`. Useful for proving that a majority
element constructed by appending sufficient copies appears in the combined list. -/
theorem mem_append_replicate_self_of_pos {α : Type u}
    (base : List α) (x : α) {n : Nat} (hn : 0 < n) :
    x ∈ base ++ List.replicate n x := by
  exact List.mem_append.mpr (Or.inr (mem_replicate_self_of_pos x hn))

/-! ## `repeatFold`: fold over replicated elements -/

/-- Repeatedly apply a binary operation `op` to `n` copies of `a`, starting from `empty`.
`repeatFold op empty n a = foldl op empty (replicate n a)`.
For example, with string append and `""`, this replicates a string `n` times;
with `(+)` and `0`, this computes `n * a`. -/
def repeatFold {α : Type} (op : α → α → α) (empty : α) (n : Nat) (a : α) : α :=
  List.foldl op empty (List.replicate n a)

/-- Size lemma for `foldl` over a replicated list. If `size` distributes over `op`
(i.e., `size (op a b) = size a + size b`), then the size after folding over `n`
copies of `a` starting from `acc` is `size acc + size a * n`. -/
theorem size_foldl_replicate
    {α : Type} (size : α → Nat) (op : α → α → α)
    (h_op : ∀ a b, size (op a b) = size a + size b)
    (n : Nat) (acc a : α) :
    size (List.foldl op acc (List.replicate n a)) = size acc + size a * n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      simp [List.replicate, ih, h_op, Nat.mul_succ]
      omega

/-- The size of `repeatFold op empty n a` is `size empty + size a * n`. -/
theorem repeatFold_size
    {α : Type} (size : α → Nat) (op : α → α → α) (empty a : α)
    (h_op : ∀ a b, size (op a b) = size a + size b) :
    ∀ n : Nat, size (repeatFold op empty n a) = size empty + size a * n := by
  intro n; exact size_foldl_replicate size op h_op n empty a

/-- When `size empty = 0`, the size of `repeatFold op empty n a` is `size a * n`. -/
theorem repeatFold_size_of_size_empty_zero
    {α : Type} (size : α → Nat) (op : α → α → α) (empty a : α)
    (h_op : ∀ a b, size (op a b) = size a + size b)
    (h_empty : size empty = 0) :
    ∀ n : Nat, size (repeatFold op empty n a) = size a * n := by
  intro n
  simpa [h_empty] using repeatFold_size size op empty a h_op n

end List

end Specific
