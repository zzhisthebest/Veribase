import Capless.Context
import Capless.Inversion.Context
import Capless.Store
import verisoftbench.Capless.Basic

/-!
# Context Inversion Lemmas for LBound

This file provides inversion lemmas for `Context.LBound` and `Context.Bound`
in extended typing contexts. These lemmas decompose lookup judgments when the context
is extended with term variables (`var`), type variables (`tvar`), capture variables
(`cvar`), or labels (`label`).

Many of the `Bound` inversion lemmas already exist in `Capless.Inversion.Context`;
this file fills in the missing `LBound` inversions and a few additional `Bound`
inversions.
-/

namespace Capless

/-! ### Bound Inversions -/

/--
Inversion lemma for `Context.Bound` under a type-variable context extension.
If a term variable `x` is bound in `Γ.tvar b`, it was already bound in `Γ`
with its type appropriately weakened.
-/
theorem Context.bound_tvar_inv
    (hb : Context.Bound (Γ.tvar b) x T) :
    ∃ T0, Context.Bound Γ x T0 ∧ T = T0.tweaken := by
  cases hb
  case there_tvar hb' => exact ⟨_, hb', rfl⟩

/-! ### LBound Inversions -/

/--
Inversion lemma for `Context.LBound` under a term-variable context extension
at a successor index (with explicit equality hypotheses).
-/
theorem Context.lbound_var_succ_inv'
    (he1 : Γ0 = Γ.var E) (he2 : x0 = x.succ)
    (hl : Context.LBound Γ0 x0 S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  cases hl <;> try (solve | cases he1 | cases he2 | aesop)

/--
Inversion lemma for `Context.LBound` under a term-variable context extension
at a successor index. If `x.succ` has an `LBound` in `Γ.var E`, then `x`
already had an `LBound` in `Γ` with its type appropriately weakened.
-/
theorem Context.lbound_var_succ_inv
    (hl : Context.LBound (Γ.var E) (x.succ) S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken :=
  Context.lbound_var_succ_inv' rfl rfl hl

/--
Inversion lemma for `Context.LBound` under a type-variable context extension.
If `x` has an `LBound` in `Γ.tvar b`, it already had an `LBound` in `Γ`
with its type appropriately weakened.
-/
theorem Context.lbound_tvar_inv
    (hl : Context.LBound (Γ.tvar b) x S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.tweaken := by
  cases hl
  case there_tvar hl' => exact ⟨_, hl', rfl⟩

/--
Inversion lemma for `Context.LBound` under a capture-variable context extension.
If `x` has an `LBound` in `Γ.cvar b`, it already had an `LBound` in `Γ`
with its type appropriately capture-weakened.
-/
theorem Context.lbound_cvar_inv
    (hl : Context.LBound (Γ.cvar b) x S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.cweaken := by
  cases hl
  case there_cvar hl' => exact ⟨_, hl', rfl⟩

/--
Inversion lemma for `Context.LBound` under a label context extension
at a successor index (with explicit equality hypotheses).
-/
theorem Context.lbound_label_succ_inv'
    (he1 : Γ0 = Γ.label S') (he2 : x0 = x.succ)
    (hl : Context.LBound Γ0 x0 S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  cases hl <;> try (solve | cases he1 | cases he2 | aesop)

/--
Inversion lemma for `Context.LBound` under a label context extension
at a successor index. If `x.succ` has an `LBound` in `Γ.label S'`, then `x`
already had an `LBound` in `Γ` with its type appropriately weakened.
-/
theorem Context.lbound_label_succ_inv
    (hl : Context.LBound (Γ.label S') (x.succ) S) :
    ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken :=
  Context.lbound_label_succ_inv' rfl rfl hl

/-! ### TBinding weakening inversion lemmas -/

/--
If `b.weaken` equals `TBinding.bound S`, then `b` must also be a `TBinding.bound`.
In other words, an `inst` binding cannot become a `bound` binding via weakening.
-/
lemma TBinding.weaken_eq_bound {b : TBinding n m k} {S : SType (n+1) m k}
    (h : b.weaken = TBinding.bound S) : ∃ S0, b = TBinding.bound S0 := by
  cases b
  · exact ⟨_, rfl⟩
  · dsimp [TBinding.weaken, TBinding.rename] at h
    injection h

/--
If `b.tweaken` equals `TBinding.bound S`, then `b` must also be a `TBinding.bound`.
-/
lemma TBinding.tweaken_eq_bound {b : TBinding n m k} {S : SType n (m+1) k}
    (h : b.tweaken = TBinding.bound S) : ∃ S0, b = TBinding.bound S0 := by
  cases b
  · exact ⟨_, rfl⟩
  · dsimp [TBinding.tweaken, TBinding.trename] at h
    injection h

/--
If `b.cweaken` equals `TBinding.bound S`, then `b` must also be a `TBinding.bound`.
-/
lemma TBinding.cweaken_eq_bound {b : TBinding n m k} {S : SType n m (k+1)}
    (h : b.cweaken = TBinding.bound S) : ∃ S0, b = TBinding.bound S0 := by
  cases b
  · exact ⟨_, rfl⟩
  · dsimp [TBinding.cweaken, TBinding.crename] at h
    injection h

/-! ### TBound inversion lemmas -/

/--
Inversion lemma for `Context.TBound` under a type-variable context extension `Γ.tvar b_tvar`.
If a type variable `X` is bound in `Γ.tvar b_tvar`, either:
- `X = 0` (the newly bound variable) and its binding is `b_tvar.tweaken`, or
- `X = x.succ` for some `x` that was already bound in `Γ` with the binding tweakened.
-/
lemma TBound.inv_tvar {Γ : Context n m k} {b_tvar : TBinding n m k}
    {X : Fin (m+1)} {b : TBinding n (m+1) k}
    (h : Context.TBound (Γ.tvar b_tvar) X b) :
    (X = 0 ∧ b = b_tvar.tweaken) ∨
    (∃ (x : Fin m) (b' : TBinding n m k), X = x.succ ∧ b = b'.tweaken ∧ Context.TBound Γ x b') := by
  cases h
  case here => left; constructor <;> rfl
  case there_tvar h' =>
    right; refine ⟨_, _, rfl, rfl, h'⟩

/--
Inversion lemma for `Context.TBound` under a term-variable context extension `Γ.var E`.
If a type variable `X` is bound in `Γ.var E`, it was already bound in `Γ`
with its binding appropriately weakened.
-/
lemma TBound.inv_var {Γ : Context n m k} {E : CType n m k}
    {X : Fin m} {b : TBinding (n+1) m k}
    (h : Context.TBound (Γ.var E) X b) :
    (∃ (b' : TBinding n m k), b = b'.weaken ∧ Context.TBound Γ X b') := by
  cases h
  case there_var h' =>
    refine ⟨_, rfl, h'⟩

/--
Inversion lemma for `Context.TBound` under a capture-variable context extension `Γ.cvar b_cvar`.
If a type variable `X` is bound in `Γ.cvar b_cvar`, it was already bound in `Γ`
with its binding appropriately capture-weakened.
-/
lemma TBound.inv_cvar {Γ : Context n m k} {b_cvar : CBinding n k}
    {X : Fin m} {b : TBinding n m (k+1)}
    (h : Context.TBound (Γ.cvar b_cvar) X b) :
    (∃ (b' : TBinding n m k), b = b'.cweaken ∧ Context.TBound Γ X b') := by
  cases h
  case there_cvar h' =>
    refine ⟨_, rfl, h'⟩

/--
Inversion lemma for `Context.TBound` under a label context extension `Γ.label S`.
If a type variable `X` is bound in `Γ.label S`, it was already bound in `Γ`
with its binding appropriately weakened.
-/
lemma TBound.inv_label {Γ : Context n m k} {S : SType n m k}
    {X : Fin m} {b : TBinding (n+1) m k}
    (h : Context.TBound (Γ.label S) X b) :
    (∃ (b' : TBinding n m k), b = b'.weaken ∧ Context.TBound Γ X b') := by
  cases h
  case there_label h' =>
    refine ⟨_, rfl, h'⟩

/-! ### Uniqueness of type variable bindings -/

open Fin

/--
`Context.TBound` is deterministic: if a type variable `X` has two bindings `b1` and `b2`
in context `Γ`, then `b1 = b2`.
-/
lemma Context.TBound.unique {Γ : Context n m k} {X : Fin m} {b1 b2 : TBinding n m k}
    (hb1 : Context.TBound Γ X b1) (hb2 : Context.TBound Γ X b2) : b1 = b2 := by
  induction Γ with
  | empty => cases hb1
  | var Γ' E ih =>
    rcases TBound.inv_var hb1 with ⟨b1', hb1_eq, hb1'⟩
    rcases TBound.inv_var hb2 with ⟨b2', hb2_eq, hb2'⟩
    rw [hb1_eq, hb2_eq]
    rw [ih hb1' hb2']
  | tvar Γ' b_tvar ih =>
    rcases TBound.inv_tvar hb1 with (⟨hX1, hb1_eq⟩ | ⟨x1, b1', hX1, hb1_eq, hb1'⟩)
    · rcases TBound.inv_tvar hb2 with (⟨hX2, hb2_eq⟩ | ⟨x2, b2', hX2, hb2_eq, hb2'⟩)
      · rw [hb1_eq, hb2_eq]
      · rw [hX1] at hX2
        exact absurd hX2.symm (Fin.succ_ne_zero x2)
    · rcases TBound.inv_tvar hb2 with (⟨hX2, hb2_eq⟩ | ⟨x2, b2', hX2, hb2_eq, hb2'⟩)
      · rw [hX1] at hX2
        exact absurd hX2 (Fin.succ_ne_zero x1)
      · rw [hb1_eq, hb2_eq]
        have hx : x1 = x2 := Fin.succ_inj.mp (by rw [← hX1, hX2])
        subst hx
        rw [ih hb1' hb2']
  | cvar Γ' b_cvar ih =>
    rcases TBound.inv_cvar hb1 with ⟨b1', hb1_eq, hb1'⟩
    rcases TBound.inv_cvar hb2 with ⟨b2', hb2_eq, hb2'⟩
    rw [hb1_eq, hb2_eq]
    rw [ih hb1' hb2']
  | label Γ' S ih =>
    rcases TBound.inv_label hb1 with ⟨b1', hb1_eq, hb1'⟩
    rcases TBound.inv_label hb2 with ⟨b2', hb2_eq, hb2'⟩
    rw [hb1_eq, hb2_eq]
    rw [ih hb1' hb2']

/--
If a type variable `X` has an `inst` binding to both `S1` and `S2`, then `S1 = S2`.
-/
lemma Context.TBound.inst_unique {Γ : Context n m k} {X : Fin m} {S1 S2 : SType n m k}
    (hb1 : Context.TBound Γ X (TBinding.inst S1))
    (hb2 : Context.TBound Γ X (TBinding.inst S2)) : S1 = S2 := by
  have h_unique := Context.TBound.unique hb1 hb2
  injection h_unique

/-! ### Tight contexts have no bound type variables -/

/--
In a tight context `Γ.IsTight`, no type variable can have a `TBinding.bound` binding.
Only `TBinding.inst` bindings are allowed in tight contexts.
-/
lemma Context.IsTight.no_tbound_bound (ht : Γ.IsTight) (hb : Context.TBound Γ X (TBinding.bound S)) :
    False := by
  have only_inst {n m k} {Γ : Context n m k} (ht : Γ.IsTight)
      {X b} (hb : Context.TBound Γ X b) : ∃ S, b = TBinding.inst S := by
    induction ht with
    | empty => cases hb
    | var _ ih =>
      cases hb with
      | there_var hb =>
        obtain ⟨S, rfl⟩ := ih hb
        exact ⟨_, rfl⟩
    | tvar _ ih =>
      cases hb with
      | here => exact ⟨_, rfl⟩
      | there_tvar hb =>
        obtain ⟨S, rfl⟩ := ih hb
        exact ⟨_, rfl⟩
    | cvar _ ih =>
      cases hb with
      | there_cvar hb =>
        obtain ⟨S, rfl⟩ := ih hb
        exact ⟨_, rfl⟩
    | label _ ih =>
      cases hb with
      | there_label hb =>
        obtain ⟨S, rfl⟩ := ih hb
        exact ⟨_, rfl⟩
  obtain ⟨_, h⟩ := only_inst ht hb
  cases h

/-! ### CBound inversion under cvar -/

/--
Inversion lemma for `Context.CBound` under a capture-variable context extension
where the outer binding is `CBinding.bound b0` and the result is `CBinding.inst C`.
Given explicit equality hypotheses (for dependent pattern-matching compatibility),
this decomposes the judgment into an inner `Context.CBound` and relates the
capture variable and capture set.

This variant with explicit equality hypotheses is useful for proofs where
the context and binding are given as variables that need to be substituted.
-/
theorem Context.cvar_bound_cvar_inst_inv'_1 {Γ : Context n m k}
  (he1 : Γ' = Context.cvar Γ (CBinding.bound b0))
  (he2 : b' = CBinding.inst C)
  (hb : Context.CBound Γ' c b') :
  ∃ c0 C0, c = c0.succ ∧ C = C0.cweaken ∧ Context.CBound Γ c0 (CBinding.inst C0) := by
  subst he1
  cases hb
  case here =>
    exfalso
    exact CBinding.bound_cweaken_ne_inst he2
  case there_cvar hb_inner =>
    rename_i c_inner b_inner
    rcases CBinding.eq_inst_of_cweaken_inst he2 with ⟨C0, h_b, h_C⟩
    refine ⟨c_inner, C0, rfl, h_C, ?_⟩
    rw [h_b] at hb_inner
    exact hb_inner

end Capless
