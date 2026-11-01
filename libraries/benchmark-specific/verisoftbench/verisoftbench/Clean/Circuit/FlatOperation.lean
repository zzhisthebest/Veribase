import Clean.Circuit.Theorems

/-!
Theorems about `FlatOperation.forAll`, `FlatOperation.proverEnvironment`,
`FlatOperation.dynamicWitnesses`, and related definitions from `Clean.Circuit`.
-/

namespace FlatOperation

/-- `forAll_nil` reduces `forAll` on the empty list to `True`. -/
@[simp]
theorem forAll_nil {F : Type} [Field F] {condition : Condition F} {offset : ℕ} :
    FlatOperation.forAll offset condition [] = True := rfl

/-- `forAll_cons` equivalence for `FlatOperation`. -/
theorem forAll_cons {F : Type} [Field F] {condition : Condition F} {offset : ℕ} {op : FlatOperation F}
    {ops : List (FlatOperation F)} :
    FlatOperation.forAll offset condition (op :: ops) ↔
      condition.applyFlat offset op ∧ FlatOperation.forAll (op.singleLocalLength + offset) condition ops := by
  cases op <;> simp [FlatOperation.forAll, Condition.applyFlat, FlatOperation.singleLocalLength]

/-- For operations with `singleLocalLength = 0` (i.e., `assert` or `lookup`),
    `proverEnvironment` ignores them and just recurses on the tail. -/
lemma proverEnvironment_cons_eq_of_singleLocalLength_zero {F : Type} [Field F] {op : FlatOperation F}
    {ops : List (FlatOperation F)} (h_sl : op.singleLocalLength = 0) (init : List F) :
    FlatOperation.proverEnvironment (op :: ops) init = FlatOperation.proverEnvironment ops init := by
  rcases op with (⟨m, c⟩ | e | l)
  · -- witness case: m = 0 from h_sl, so the witness vector is empty
    have hm : m = 0 := by simpa [FlatOperation.singleLocalLength] using h_sl
    subst hm
    have h_dw : FlatOperation.dynamicWitness (.witness 0 c : FlatOperation F) init = [] := by
      simp [FlatOperation.dynamicWitness]
    simp [FlatOperation.proverEnvironment, dynamicWitnesses_cons, h_dw]
  · simp [FlatOperation.proverEnvironment, dynamicWitnesses_cons, FlatOperation.dynamicWitness]
  · simp [FlatOperation.proverEnvironment, dynamicWitnesses_cons, FlatOperation.dynamicWitness]

/-- `proverEnvironment` for a witness cons: the witness values are appended to `init`. -/
lemma proverEnvironment_cons_witness {F : Type} [Field F] (m : ℕ) (c : Environment F → Vector F m) (init : List F)
    (ops : List (FlatOperation F)) :
    FlatOperation.proverEnvironment (.witness m c :: ops) init =
    FlatOperation.proverEnvironment ops (init ++ (c (.fromList init)).toList) := by
  simp [FlatOperation.proverEnvironment, dynamicWitnesses_cons, FlatOperation.dynamicWitness]

/-- The prover environment for a witness cons agrees with `.fromList init` below `init.length`. -/
lemma proverEnvironment_witness_agreesBelow {F : Type} [Field F] (m : ℕ) (c : Environment F → Vector F m) (init : List F)
    (ops : List (FlatOperation F)) :
    (FlatOperation.proverEnvironment (.witness m c :: ops) init).AgreesBelow init.length (.fromList init) := by
  intro i hi
  simp [FlatOperation.proverEnvironment, Environment.fromList]
  rw [getElem?_dynamicWitnesses_of_lt hi]
  simp [hi]

/-- Extract the tail `forAll` condition from a cons whose head has `singleLocalLength = 0`
    (i.e., is an `assert` or `lookup`). -/
lemma forAll_of_cons_nonWitness {F : Type} [Field F] {condition : Condition F} {offset : ℕ} {op : FlatOperation F}
    (h_sl : op.singleLocalLength = 0) {ops : List (FlatOperation F)}
    (h : FlatOperation.forAll offset condition (op :: ops)) : FlatOperation.forAll offset condition ops := by
  rcases (forAll_cons (op := op) (ops := ops)).mp h with ⟨_, h_forall⟩
  simpa [h_sl] using h_forall

/-- The prover environment entry at offset `init.length + i` for a witness cons equals
    the `i`-th entry of the witness vector evaluated at `.fromList init`. -/
lemma proverEnvironment_witness_get_val {F : Type} [Field F] (m : ℕ) (c : Environment F → Vector F m) (init : List F)
    (ops : List (FlatOperation F)) (i : Fin m) :
    (FlatOperation.proverEnvironment (.witness m c :: ops) init).get (init.length + i.val) =
    (c (.fromList init))[i.val] := by
  let pe := FlatOperation.proverEnvironment (.witness m c :: ops) init
  have hi_val : (i : ℕ) < ((.witness m c : FlatOperation F)).singleLocalLength := by
    simp [FlatOperation.singleLocalLength, i.2]
  have h1 : pe.get (init.length + i.val) =
      (dynamicWitnesses (.witness m c :: ops) init)[init.length + i.val]?.getD 0 := by
    simp [pe, FlatOperation.proverEnvironment, Environment.fromList]
  have htemp := getElem?_dynamicWitnesses_cons_right (op := (.witness m c : FlatOperation F))
    (ops := ops) (init := init) hi_val
  have h2 : (dynamicWitnesses (.witness m c :: ops) init)[init.length + i.val]?.getD 0
          = ((c (.fromList init)).toList)[i.val] := by
    rw [htemp]
    simp [FlatOperation.dynamicWitness]
  have h3 : ((c (.fromList init)).toList)[i.val] = (c (.fromList init))[i.val] := by
    have h_len : (i : ℕ) < ((c (.fromList init)).toList).length := by
      simp [i.2]
    simp [Vector.getElem_toList (xs := c (.fromList init)) (i := i.val) (h := h_len)]
  rw [h1, h2, h3]

/-- The length of `init` extended by a witness vector of length `m` is `m + init.length`. -/
lemma length_init_extend_witness {F : Type} [Field F] (m : ℕ) (c : Environment F → Vector F m) (init : List F) :
    (init ++ (c (.fromList init)).toList).length = m + init.length := by
  simp [add_comm]

/-- Under the computable-witnesses hypothesis on a witness cons, the prover environment
    extends the vector with the witness values. -/
lemma proverEnvironment_witness_extendsVector {F : Type} [Field F] {m : ℕ} {c : Environment F → Vector F m}
    {init : List F} {ops : List (FlatOperation F)}
    (h_forall : ∀ (env env' : Environment F),
      FlatOperation.forAll init.length { witness n _ c := env.AgreesBelow n env' → c env = c env' }
        (.witness m c :: ops)) :
    (FlatOperation.proverEnvironment (.witness m c :: ops) init).ExtendsVector
      (c (FlatOperation.proverEnvironment (.witness m c :: ops) init)) init.length := by
  let pe := FlatOperation.proverEnvironment (.witness m c :: ops) init
  have hagrees : pe.AgreesBelow init.length (.fromList init) :=
    proverEnvironment_witness_agreesBelow m c init ops
  have h_c_eq : c pe = c (.fromList init) := by
    have h_all := h_forall pe (.fromList init)
    rcases (forAll_cons (op := .witness m c) (ops := ops)).mp h_all with ⟨h_witness, _⟩
    exact h_witness hagrees
  intro i
  have h_eq : pe.get (init.length + i.val) = (c (.fromList init))[i.val] :=
    proverEnvironment_witness_get_val m c init ops i
  rw [h_c_eq, h_eq]

theorem proverEnvironment_usesLocalWitnesses_1 {F : Type} [Field F] {ops : List (FlatOperation F)} (init : List F) :
  (∀ (env env' : Environment F),
    FlatOperation.forAll init.length { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops) →
    (FlatOperation.proverEnvironment ops init).UsesLocalWitnessesFlat init.length ops := by
  intro h
  induction ops using FlatOperation.induct generalizing init with
  | empty =>
    simp [Environment.UsesLocalWitnessesFlat, FlatOperation.forAll]

  | assert e ops ih =>
    have h_assert_sl : ((.assert e : FlatOperation F)).singleLocalLength = 0 := by
      simp [FlatOperation.singleLocalLength]
    have h_ops : ∀ (env env' : Environment F),
      FlatOperation.forAll init.length
        { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops := by
      intro env env'
      exact forAll_of_cons_nonWitness h_assert_sl (h env env')
    have ih_result := ih init h_ops
    have h_pe : FlatOperation.proverEnvironment (assert e :: ops) init =
        FlatOperation.proverEnvironment ops init :=
      proverEnvironment_cons_eq_of_singleLocalLength_zero h_assert_sl init
    simpa [Environment.UsesLocalWitnessesFlat, FlatOperation.forAll, h_pe] using ih_result

  | lookup l ops ih =>
    have h_lookup_sl : ((.lookup l : FlatOperation F)).singleLocalLength = 0 := by
      simp [FlatOperation.singleLocalLength]
    have h_ops : ∀ (env env' : Environment F),
      FlatOperation.forAll init.length
        { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops := by
      intro env env'
      exact forAll_of_cons_nonWitness h_lookup_sl (h env env')
    have ih_result := ih init h_ops
    have h_pe : FlatOperation.proverEnvironment (lookup l :: ops) init =
        FlatOperation.proverEnvironment ops init :=
      proverEnvironment_cons_eq_of_singleLocalLength_zero h_lookup_sl init
    simpa [Environment.UsesLocalWitnessesFlat, FlatOperation.forAll, h_pe] using ih_result

  | witness m c ops ih =>
    let pe := FlatOperation.proverEnvironment (.witness m c :: ops) init
    let init' := init ++ (c (.fromList init)).toList

    have h_len_eq : init'.length = m + init.length :=
      length_init_extend_witness m c init

    have h_ops : ∀ (env env' : Environment F),
      FlatOperation.forAll init'.length
        { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops := by
      intro env env'
      have h_all := h env env'
      rcases (forAll_cons (op := .witness m c) (ops := ops)).mp h_all with ⟨_, h_forall⟩
      simpa [h_len_eq, add_comm] using h_forall

    have ih_result := ih init' h_ops

    have h_pe_eq : FlatOperation.proverEnvironment ops init' = pe :=
      (proverEnvironment_cons_witness m c init ops).symm

    have h_first : pe.ExtendsVector (c pe) init.length :=
      proverEnvironment_witness_extendsVector h

    have h_second : FlatOperation.forAll (m + init.length)
      { witness n _ compute := pe.ExtendsVector (compute pe) n } ops := by
      have h_goal : (FlatOperation.proverEnvironment ops init').UsesLocalWitnessesFlat init'.length ops := ih_result
      simpa [Environment.UsesLocalWitnessesFlat, h_len_eq, h_pe_eq] using h_goal

    simp [Environment.UsesLocalWitnessesFlat, FlatOperation.forAll]
    exact And.intro h_first h_second

/-- `localWitnesses` distributes over `++` for flat operations, as arrays. -/
lemma localWitnesses_flat_append {F : Type} [Field F] {ops1 ops2 : List (FlatOperation F)} {env : Environment F} :
    (localWitnesses env (ops1 ++ ops2)).toArray = (localWitnesses env ops1).toArray ++ (localWitnesses env ops2).toArray := by
  induction ops1 with
  | nil => simp [localWitnesses]
  | cons op ops1 ih =>
    cases op with
    | witness m c =>
      simp [localWitnesses, ih]
    | assert e =>
      simp [localWitnesses, ih]
    | lookup l =>
      simp [localWitnesses, ih]

/-- `Subcircuit.witnesses` as an array equals `localWitnesses` of the subcircuit's flat ops. -/
lemma subcircuit_witnesses_toArray {F : Type} [Field F] {n} (s : Subcircuit F n) (env : Environment F) :
    (s.witnesses env).toArray = (localWitnesses env s.ops).toArray := by
  simp [Subcircuit.witnesses, Vector.toArray_cast]

/-- `Operations.toFlat` distributes over `++`. -/
lemma toFlat_append {F : Type} [Field F] (ops1 ops2 : Operations F) :
    (ops1 ++ ops2).toFlat = ops1.toFlat ++ ops2.toFlat := by
  induction ops1 using Operations.induct with
  | empty => rfl
  | witness m c ops ih => simp [Operations.toFlat, ih]
  | assert e ops ih => simp [Operations.toFlat, ih]
  | lookup l ops ih => simp [Operations.toFlat, ih]
  | subcircuit s ops ih => simp [Operations.toFlat, ih, List.append_assoc]

/-- `localWitnesses` on flattened operations equals `Operations.localWitnesses`, as arrays. -/
lemma localWitnesses_toFlat_toArray {F : Type} [Field F] {ops : Operations F} {env} :
    (localWitnesses env ops.toFlat).toArray = (ops.localWitnesses env).toArray := by
  induction ops using Operations.induct with
  | empty => rfl
  | witness m c ops ih =>
    simp [Operations.toFlat, Operations.localWitnesses, FlatOperation.localWitnesses, ih]
  | assert e ops ih =>
    simp [Operations.toFlat, Operations.localWitnesses, FlatOperation.localWitnesses, ih]
  | lookup l ops ih =>
    simp [Operations.toFlat, Operations.localWitnesses, FlatOperation.localWitnesses, ih]
  | subcircuit s ops ih =>
    simp [Operations.toFlat, Operations.localWitnesses, Subcircuit.witnesses,
      localWitnesses_flat_append, ih]

end FlatOperation
