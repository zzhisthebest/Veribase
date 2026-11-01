import Capless.Store
import Capless.Type.Value
import verisoftbench.Capless.Inversion.Context
import Capless.Inversion.Subtyping

/-!
# Store Lookup Inversion Lemmas

Lemmas relating store bindings (`Store.Bound`) to typing judgments
(`Typed`, `TypedStore`), used for soundness and progress proofs.

These build on `Store.lookup_exists` from `Capless.Soundness.Progress` by
using typing information to select the appropriate branch (value vs. label).
-/

namespace Capless

/--
If a variable `x` is typed with `EType.type T` where `T.IsValue`, and the store
is well-typed, then `x` is bound to a value `v` in the store.

This is the value case of `Store.lookup_exists` specialized with typing information.
-/
theorem Store.val_lookup_exists {σ : Store n m k} {x : Fin n}
    (hs : TypedStore σ Γ) (hx : Typed Γ (Term.var x) (EType.type T) Cx)
    (hvt : T.IsValue) :
    ∃ v, Store.Bound σ x v ∧ v.IsValue := by
  let rec value_source {n m k : Nat} {Γ : Context n m k}
      {S1 S2 V : SType n m k} (hs : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
      (hd : SType.Dealias Γ S2 V) (hv : V.IsValue) :
      ∃ V1, SType.Dealias Γ S1 V1 ∧ V1.IsValue := by
    match hs with
    | .top => cases hd; cases hv
    | .refl => exact ⟨_, hd, hv⟩
    | .trans h1 h2 =>
      obtain ⟨Vm, hdm, hvm⟩ := value_source h2 ht hd hv
      exact value_source h1 ht hdm hvm
    | .tvar hb => exact False.elim (ht.no_tbound_bound hb)
    | .tinstl hb =>
      cases hd with
      | refl => cases hv
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ⟨_, hd', hv⟩
    | .tinstr hb => exact ⟨_, .step hb hd, hv⟩
    | .boxed _ => exact ⟨_, .refl, .box⟩
    | .label _ => cases hd; cases hv
    | .xforall _ _ => exact ⟨_, .refl, .xforall⟩
    | .tforall _ _ => exact ⟨_, .refl, .tforall⟩
    | .cforall _ _ => exact ⟨_, .refl, .cforall⟩
  have value_var_bound {n m k : Nat} {Γ : Context n m k}
      {t : Term n m k} {E : EType n m k} {Ct C : CaptureSet n k}
      {x : Fin n} {S V : SType n m k} (h : Typed Γ t E Ct) (ht : Γ.IsTight)
      (he : t = Term.var x) (hE : E = EType.type (CType.capt C S))
      (hd : SType.Dealias Γ S V) (hv : V.IsValue) :
      ∃ T, Context.Bound Γ x T := by
    induction h with
    | var hb => cases he; exact ⟨_, hb⟩
    | label hb => cases hE; cases hd; cases hv
    | sub h hc hs ih =>
      cases hs with
      | exist hs => cases hE
      | type hs => cases hs with
        | capt hc' hs =>
          cases hE
          obtain ⟨V1, hd1, hv1⟩ := value_source hs ht hd hv
          exact ih ht he rfl hd1 hv1
    | _ => cases he
  have store_tight {n m k : Nat} {σ : Store n m k} {Γ : Context n m k}
      (h : TypedStore σ Γ) : Γ.IsTight := by
    induction h <;> constructor <;> assumption
  have store_value_of_bound {n m k : Nat} {σ : Store n m k} {Γ : Context n m k}
      {x : Fin n} {T : CType n m k} (h : TypedStore σ Γ) (hb : Context.Bound Γ x T) :
      ∃ v, Store.Bound σ x v ∧ v.IsValue := by
    induction h with
    | empty => cases hb
    | val hs ht hv ih =>
      cases hb with
      | here => exact ⟨_, .here, by cases hv <;> constructor⟩
      | there_var hb =>
        obtain ⟨v, hb, hv⟩ := ih hb
        exact ⟨_, .there_val hb, by cases hv <;> constructor⟩
    | tval hs ih =>
      cases hb with
      | there_tvar hb =>
        obtain ⟨v, hb, hv⟩ := ih hb
        exact ⟨_, .there_tval hb, by cases hv <;> constructor⟩
    | cval hs ih =>
      cases hb with
      | there_cvar hb =>
        obtain ⟨v, hb, hv⟩ := ih hb
        exact ⟨_, .there_cval hb, by cases hv <;> constructor⟩
    | label hs ih =>
      cases hb with
      | there_label hb =>
        obtain ⟨v, hb, hv⟩ := ih hb
        exact ⟨_, .there_label hb, by cases hv <;> constructor⟩
  cases hvt with
  | capt hv =>
    obtain ⟨T0, hb⟩ := value_var_bound hx (store_tight hs) rfl rfl .refl hv
    exact store_value_of_bound hs hb

end Capless
