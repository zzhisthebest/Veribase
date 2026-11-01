import Clean.Circuit.Loops
import Clean.Utils.Vector
import verisoftbench.Common.List.Basic

/-!
Theorems about loop constructs (`foldlM`, `foldl`, `foldl.foldlAcc`, etc.)
from `Clean.Circuit.Loops`.
-/

namespace Circuit

/-! ### General bind/pure lemmas for Circuit operations -/

variable {F : Type} [Field F] {α β : Type}

/-- How `Circuit.operations` distributes over bind (`>>=`).
This is a definitional equality from the `Circuit.bind` definition. -/
lemma bind_operations_eq (f : Circuit F α) (g : α → Circuit F β) (off : ℕ) :
    (f >>= g).operations off = f.operations off ++
    (g (f.output off)).operations (off + f.localLength off) :=
  rfl

/-- `pure` on a `Circuit` produces no operations (empty operation list). -/
lemma pure_operations_eq (a : α) (off : ℕ) :
    (pure a : Circuit F α).operations off = [] :=
  rfl

/-- If a continuation `g` returns `pure`, then `bind` contributes no additional operations.
This is a common pattern when using `bind` only for plumbing (e.g. appending to a vector). -/
lemma bind_pure_operations_eq (f : Circuit F α) (h : α → β) (off : ℕ) :
    (f >>= (fun a => pure (h a))).operations off = f.operations off := by
  rw [bind_operations_eq, pure_operations_eq, List.append_nil]

namespace ForM

variable {n m : ℕ} {F : Type} [Field F] {α : Type}
variable {circuit : α → Circuit F Unit} {xs : Vector α m}

/-- `Vector.forM` of a unit-returning circuit produces a circuit whose output is always `()`. -/
lemma forM_output_unit {n : ℕ} :
    (xs.forM circuit).output n = () := rfl

/-- For any circuit returning `Unit`, the output state component is always `PUnit.unit`. -/
lemma circuit_unit_output (c : Circuit F Unit) (k : ℕ) : (c k).1 = PUnit.unit := by
  simp

/-- Reduction of `Vector.forM` operations to `List.foldlM` operations. -/
lemma vector_forM_operations_eq (xs : Vector α m) (f : α → Circuit F Unit) (k : ℕ) :
    (xs.forM f).operations k =
      ((xs.toArray.toList).foldlM (fun (_ : PUnit) (x : α) => f x) PUnit.unit).operations k := by
  have h : xs.forM f = xs.toArray.forM f := rfl
  rw [h, Array.forM, Array.foldlM_toList.symm]

/-- If each `f a` has local length `L` for all offsets, then the operations of `foldlM`
    over a list are the concatenation of individual operations with shifted indices. -/
lemma list_foldlM_operations_eq_of_const_length {L : ℕ} (f : α → Circuit F Unit)
    (h_len : ∀ a k, (f a).localLength k = L) (l : List α) (k : ℕ) :
    ((l.foldlM (fun (_ : PUnit) (x : α) => f x) PUnit.unit).operations k) =
      (List.ofFn fun (i : Fin l.length) => (f l[i.val]).operations (k + i.val * L)).flatten := by
  induction l generalizing k with
  | nil =>
      simp [pure, Circuit.operations, List.foldlM]
  | cons x l ih =>
      simp [List.foldlM, Circuit.bind_def, Circuit.operations, h_len x, circuit_unit_output (f x)]
      simpa [add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm]
        using ih (k + L)

/-- Under `ConstantLength`, the operations of `Vector.forM` decompose as the flattened
    list of per-element circuit operations, each offset by the constant local length
    times the element index. -/
theorem operations_eq_forM_of_const_length (constant : ConstantLength circuit) (n : ℕ) :
    (xs.forM circuit).operations n =
      (List.ofFn fun (i : Fin m) => (circuit xs[i.val]).operations (n + i * constant.localLength)).flatten := by
  rw [vector_forM_operations_eq xs circuit n]
  have h_len : xs.toArray.toList.length = m := by
    simp [Vector.size_toArray]
  calc
    ((xs.toArray.toList).foldlM (fun (_ : PUnit) (x : α) => circuit x) PUnit.unit).operations n =
        (List.ofFn fun (i : Fin xs.toArray.toList.length) =>
          (circuit (xs.toArray.toList)[i.val]).operations (n + i.val * constant.localLength)).flatten :=
      list_foldlM_operations_eq_of_const_length circuit constant.localLength_eq (xs.toArray.toList) n
    _ = (List.ofFn fun (i : Fin m) => (circuit xs[i.val]).operations (n + i * constant.localLength)).flatten := by
      simp [h_len]

end ForM

namespace FoldlM

variable {n m : ℕ} {F : Type} [Field F] {α β : Type}
variable {prop : Condition F} {xs : Vector α m}
variable {circuit : β → α → Circuit F β} {init : β}
variable [Inhabited β] [Inhabited α]

/-! ### Vector foldlM and Circuit bind lemmas -/

/-- `Vector.foldlM` is equivalent to folding over the corresponding list via `toList`. -/
theorem foldlM_toList {n' : Nat} (xs' : Vector α n') {m' : Type → Type} [Monad m'] (f : β → α → m' β)
    (b : β) : xs'.foldlM f b = xs'.toList.foldlM f b := by
  simp only [Vector.foldlM, Vector.toList, Array.foldlM_toList]

/-- `foldlM` on `Vector.cons` decomposes into the first step and the rest. -/
lemma foldlM_cons_eq {m' : ℕ} (x : α) (xs' : Vector α m') (c : β → α → Circuit F β) (b : β) :
    (Vector.cons x xs').foldlM c b = (do
      let b' ← c b x
      xs'.foldlM c b') := by
  simp [foldlM_toList, Vector.cons, Vector.toList, List.foldlM_cons]

/-! ### ConstantOutput and ConstantLength lemmas -/

/-- Under `ConstantOutput`, all circuit outputs are equal to the default output. -/
lemma constantOutput_eq {circuit : β → α → Circuit F β}
    (h_const_out : ConstantOutput (prod circuit)) (b : β) (a : α) (n' : ℕ) :
    (circuit b a).output n' = (circuit (default : β) (default : α)).output n' := by
  exact h_const_out (b, a) n'

/-- Under `ConstantLength`, all circuit `localLength` values (at default offset) are equal
to the default. -/
lemma constantLength_eq {circuit : β → α → Circuit F β}
    (h_constant : ConstantLength (prod circuit)) (b : β) (a : α) (n' : ℕ) :
    (circuit b a).localLength n' = (circuit (default : β) (default : α)).localLength := by
  exact (h_constant.localLength_eq (b, a) n').trans
    (h_constant.localLength_eq (default, default) 0).symm

/-- Under `ConstantLength`, `localLength` (at offset 0) is the same for any accumulator
and vector element. -/
lemma constantLength_all_eq {circuit : β → α → Circuit F β}
    (h_constant : ConstantLength (prod circuit)) {m' : ℕ} (xs' : Vector α m')
    (acc : β) (j : Fin m') :
    (circuit acc xs'[j.val]).localLength = (circuit (default : β) (default : α)).localLength := by
  exact constantLength_eq h_constant acc xs'[j.val] 0

/-! ### Helper lemmas for `Fin.foldl` and `foldlAcc` -/

/-- `Fin.foldl` with a constant function (ignoring accumulator) simplifies to the
last element. -/
lemma fin_foldl_const_val_simple {α' : Type} {i : ℕ} (f : ℕ → α') (init' : α') :
    Fin.foldl (i + 1) (fun _ j => f j.val) init' = f i := by
  simp [Fin.foldl_succ_last]

/-- `foldlAcc` at a successor index shifts when cons-ing at the front. -/
lemma foldlAcc_cons_succ {circuit : β → α → Circuit F β}
    (h_constant : ConstantLength (prod circuit)) {m' : ℕ} (x : α) (xs' : Vector α m')
    (b : β) (n' : ℕ) (i : Fin m') :
    foldlAcc n' (Vector.cons x xs') circuit b i.succ =
      foldlAcc (n' + (circuit b x).localLength n') xs' circuit ((circuit b x).output n') i := by
  unfold foldlAcc
  simp only [Fin.val_succ]
  rw [Fin.foldl_succ]
  simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Vector.cons,
    Fin.val_succ]
  simp only [Vector.getElem_append, Vector.getElem_mk, Array.getElem_singleton,
    Vector.size, Nat.lt_one_iff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  congr 1
  funext acc j
  simp only [constantLength_eq h_constant]
  congr 1
  simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- `foldlAcc` at step `i+1` simplifies under `ConstantOutput` and `ConstantLength`. -/
theorem foldlAcc_const_succ (h_const_out : ConstantOutput (prod circuit))
    [constant : ConstantLength (prod circuit)] (i : ℕ) (hi : i + 1 < m) :
    foldlAcc n xs circuit init ⟨i + 1, hi⟩ =
      (circuit default xs[i]).output (n + i * (circuit default default).localLength) := by
  unfold foldlAcc
  rw [Fin.foldl_succ_last]
  simp only [Fin.val_last]
  rw [constantLength_eq constant]
  exact (constantOutput_eq h_const_out _ _ _).trans
    (constantOutput_eq h_const_out _ _ _).symm

/-! ### Decomposition of `foldlM` circuit operations -/

/-- The operations of a `foldlM` circuit decompose as the flattened list of the
per-iteration circuit operations, indexed by the accumulated output. -/
theorem operations_eq_aux {m' : ℕ} (xs' : Vector α m') (n' : ℕ) (init' : β)
    {circuit' : β → α → Circuit F β}
    [constant' : ConstantLength (prod circuit')] :
    (Vector.foldlM circuit' init' xs').operations n' =
      (List.ofFn fun i =>
        (circuit' (foldlAcc n' xs' circuit' init' i) xs'[i.val]).operations
          (n' + i * constant'.localLength)).flatten := by
  induction xs' using Vector.induct generalizing n' init' with
  | nil => simp [foldlM_toList, pure_operations_eq]
  | cons x xs ih =>
    rw [foldlM_cons_eq, bind_operations_eq, ih, List.ofFn_succ]
    simp only [List.flatten_cons]
    have hz : foldlAcc n' (Vector.cons x xs) circuit' init' 0 = init' := rfl
    rw [hz]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [foldlAcc_cons_succ constant']
    simp only [Vector.cons, Fin.val_succ, Vector.getElem_mk,
      List.getElem_cons_succ]
    congr 1
    rw [constant'.localLength_eq (init', x) n']
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- When both `ConstantLength` and `ConstantOutput` hold, the operations of a `foldlM`
circuit are the first iteration's operations followed by the flattened operations of
the remaining iterations, each specialized with the default accumulator output. -/
theorem operations_eq_const_dfyxu [NeZero m] (constant : ConstantLength (prod circuit))
    (h_const_out : ConstantOutput (prod circuit)) :
  (Vector.foldlM circuit init xs).operations n =
  (circuit init (xs[0]'(NeZero.pos m))).operations n ++
  (List.ofFn fun (⟨i, _⟩ : Fin (m - 1)) =>
    let k := (circuit default default).localLength
    let acc := (circuit default xs[i]).output (n + i*k)
    (circuit acc xs[i + 1]).operations (n + (i + 1)*k)).flatten := by
  letI := constant
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m =>
    rw [operations_eq_aux, List.ofFn_succ]
    simp only [List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.add_zero,
      Nat.add_sub_cancel]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext i
    have ha := foldlAcc_const_succ (n := n) (xs := xs) (init := init)
      h_const_out i.val (by omega)
    change foldlAcc n xs circuit init i.succ = _ at ha
    rw [ha]
    have hk : constant.localLength = (circuit default default).localLength :=
      (constant.localLength_eq (default, default) 0).symm
    simp [hk]

/-! ### forAll decomposition for foldlM -/

/-- Decompose a `foldlM` circuit's `forAll` condition into that of the first iteration
and a universal quantifier over subsequent iterations. Requires `ConstantLength` and
`ConstantOutput` on the loop body (in uncurried form via `prod`). -/
theorem forAll_iff [NeZero m] {constant : ConstantLength (prod circuit)}
    (h_const_out : ConstantOutput (prod circuit)) :
  (xs.foldlM circuit init).forAll n prop ↔
  (circuit init (xs[0]'(NeZero.pos m))).forAll n prop ∧
  ∀ (i : ℕ) (hi : i + 1 < m),
    let acc := (circuit default xs[i]).output (n + i*(circuit default default).localLength);
    (circuit acc xs[i + 1]).forAll (n + (i + 1)*(circuit default default).localLength) prop := by
  have foldl_forAll_aux {m' : ℕ} (xs' : Vector α m')
      (n' : ℕ) (init' : β) [constant' : ConstantLength (prod circuit)] :
      (xs'.foldlM circuit init').forAll n' prop ↔
        ∀ i : Fin m', (circuit (foldlAcc n' xs' circuit init' i) xs'[i.val]).forAll
          (n' + i.val * constant'.localLength) prop := by
    induction xs' using Vector.induct generalizing n' init' with
    | nil => simp [foldlM_toList, forAll, pure_operations_eq, Operations.forAll]
    | cons x xs ih =>
      rw [foldlM_cons_eq, bind_forAll', ih, Fin.forall_fin_succ]
      have hz : foldlAcc n' (Vector.cons x xs) circuit init' 0 = init' := rfl
      rw [hz]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero]
      apply and_congr Iff.rfl
      apply forall_congr'
      intro i
      rw [foldlAcc_cons_succ constant']
      simp only [Vector.cons, Fin.val_succ, Vector.getElem_mk]
      rw [constant'.localLength_eq (init', x) n']
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  letI := constant
  rw [foldl_forAll_aux]
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m =>
    rw [Fin.forall_fin_succ]
    have hz : foldlAcc n xs circuit init 0 = init := rfl
    rw [hz]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero]
    apply and_congr Iff.rfl
    have hk : constant.localLength = (circuit default default).localLength :=
      (constant.localLength_eq (default, default) 0).symm
    constructor
    · intro h i hi
      have ha := foldlAcc_const_succ (n := n) (xs := xs) (init := init)
        h_const_out i hi
      have hh := h ⟨i, by omega⟩
      change foldlAcc n xs circuit init (⟨i, by omega⟩ : Fin m).succ = _ at ha
      rw [ha] at hh
      simpa only [Fin.val_succ, ha, hk] using hh
    · intro h i
      have ha := foldlAcc_const_succ (n := n) (xs := xs) (init := init)
        h_const_out i.val (by omega)
      change foldlAcc n xs circuit init i.succ = _ at ha
      rw [ha]
      simpa only [Fin.val_succ, hk] using h i.val (by omega)

end FoldlM

namespace MapM

variable {n m : ℕ} {F : Type} [Field F] {α β : Type}
variable {circuit : α → Circuit F β} {xs : Vector α m} [constant : ConstantLength circuit]

/-- Under `ConstantLength`, the operations of `Vector.mapM` on a circuit decompose
as the flattened list of per-element operations, each offset by the constant local length
times the element index. -/
theorem operations_eq_mapM : (xs.mapM circuit).operations n =
    (List.ofFn fun (i : Fin m) => (circuit xs[i.val]).operations (n + i * constant.localLength)).flatten := by
  induction xs using Vector.inductPush with
  | nil =>
      simp [pure_operations_eq]
  | push as a ih =>
      rw [Vector.mapM_push, bind_operations_eq]
      have h_inner : (circuit a >>=
            (fun (b : β) => pure (((as.mapM circuit).output n).push b))).operations
            (n + (as.mapM circuit).localLength n) =
          (circuit a).operations (n + (as.mapM circuit).localLength n) := by
        rw [bind_pure_operations_eq]
      rw [h_inner]
      have hll_as : (as.mapM circuit).localLength n = as.size * constant.localLength :=
        localLength_eq (m := as.size) (xs := as)
      rw [hll_as]
      rw [ih]
      rw [_root_.ofFn_flatten_snoc as.size (fun (i : Fin (as.size + 1)) =>
        (circuit (as.push a)[i.val]).operations (n + i.val * constant.localLength))]
      simp

end MapM

end Circuit
