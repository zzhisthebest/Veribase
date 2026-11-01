import Capless.Renaming.Basic
import Capless.Subcapturing
import Capless.Subtyping
import verisoftbench.Capless.Basic

/-!
# Capture Variable Renaming Preserves Subtyping

This module proves that subcapturing, subbounding, and subtyping relations
are preserved under capture variable renaming. If two types are in a subtyping
relation in context `Γ`, then after renaming capture variables via a valid
`CVarMap`, they remain in the same subtyping relation in the target context `Δ`.
-/

namespace Capless

/-! ## `Subcapt` is preserved under capture variable renaming -/

/-! ### Individual constructor lemmas

These lemmas state how each constructor of `Subcapt` interacts with capture-variable
renaming via a `CVarMap`. They are useful for forward reasoning about specific
subcapturing cases without running the full induction of `Subcapt.crename`.
-/

/--
If `C1 ⊆ C2` as capture sets, then after crenaming with `f`, we have
`Δ ⊢ C1.crename f <:c C2.crename f`.
-/
theorem subcapt_crename_subset {n m k k'} {Δ : Context n m k'}
    {C1 C2 : CaptureSet n k} {f : FinFun k k'}
    (hsubset : C1 ⊆ C2) :
    Subcapt Δ (C1.crename f) (C2.crename f) :=
  Subcapt.subset (CaptureSet.crename_monotone hsubset)

/--
If `Γ` has a term variable `x` bound with type `CType.capt C S`, and
`ρ : CVarMap Γ f Δ`, then `Δ ⊢ {x=x} <:c C.crename f`.
-/
theorem subcapt_crename_var {n m k k'} {Γ : Context n m k} {Δ : Context n m k'}
    {C : CaptureSet n k} {S : SType n m k} {x : Fin n} {f : FinFun k k'}
    (hbound : Context.Bound Γ x (CType.capt C S)) (ρ : CVarMap Γ f Δ) :
    Subcapt Δ {x=x} (C.crename f) :=
  Subcapt.var (ρ.map x (CType.capt C S) hbound)

/--
If `Γ` has a capture variable `c` bound with `CBinding.inst C`, and
`ρ : CVarMap Γ f Δ`, then `Δ ⊢ C.crename f <:c {c=f c}`.
-/
theorem subcapt_crename_cinstl {n m k k'} {Γ : Context n m k} {Δ : Context n m k'}
    {C : CaptureSet n k} {c : Fin k} {f : FinFun k k'}
    (hcbound : Context.CBound Γ c (CBinding.inst C)) (ρ : CVarMap Γ f Δ) :
    Subcapt Δ (C.crename f) {c=f c} :=
  Subcapt.cinstl (ρ.cmap c (CBinding.inst C) hcbound)

/--
If `Γ` has a capture variable `c` bound with `CBinding.inst C`, and
`ρ : CVarMap Γ f Δ`, then `Δ ⊢ {c=f c} <:c C.crename f`.
-/
theorem subcapt_crename_cinstr {n m k k'} {Γ : Context n m k} {Δ : Context n m k'}
    {C : CaptureSet n k} {c : Fin k} {f : FinFun k k'}
    (hcbound : Context.CBound Γ c (CBinding.inst C)) (ρ : CVarMap Γ f Δ) :
    Subcapt Δ {c=f c} (C.crename f) :=
  Subcapt.cinstr (ρ.cmap c (CBinding.inst C) hcbound)

/--
If `Γ` has a capture variable `c` bound with `CBinding.bound (CBound.upper C)`, and
`ρ : CVarMap Γ f Δ`, then `Δ ⊢ {c=f c} <:c C.crename f`.
-/
theorem subcapt_crename_cbound {n m k k'} {Γ : Context n m k} {Δ : Context n m k'}
    {C : CaptureSet n k} {c : Fin k} {f : FinFun k k'}
    (hcbound : Context.CBound Γ c (CBinding.bound (CBound.upper C))) (ρ : CVarMap Γ f Δ) :
    Subcapt Δ {c=f c} (C.crename f) :=
  Subcapt.cbound (ρ.cmap c (CBinding.bound (CBound.upper C)) hcbound)

/-! ### Main preservation theorem -/

/--
Subcapturing is preserved under capture variable renaming.
If `Γ ⊢ C1 <:c C2` and `ρ : CVarMap Γ f Δ`, then `Δ ⊢ C1.crename f <:c C2.crename f`.
-/
theorem Subcapt.crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    (h : Subcapt Γ C1 C2)
    (ρ : CVarMap Γ f Δ) :
    Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h
  case trans h1 h2 ih1 ih2 =>
    exact Subcapt.trans (ih1 ρ) (ih2 ρ)
  case subset h =>
    exact Subcapt.subset (CaptureSet.crename_monotone h)
  case union h1 h2 ih1 ih2 =>
    simpa using Subcapt.union (ih1 ρ) (ih2 ρ)
  case var x C S hb =>
    have hmap := ρ.map x (CType.capt C S) hb
    simpa [CaptureSet.crename, CType.crename] using Subcapt.var hmap
  case cinstl c C hb =>
    have hmap := ρ.cmap c (CBinding.inst C) hb
    simpa [CaptureSet.crename, CBinding.crename] using Subcapt.cinstl hmap
  case cinstr c C hb =>
    have hmap := ρ.cmap c (CBinding.inst C) hb
    simpa [CaptureSet.crename, CBinding.crename] using Subcapt.cinstr hmap
  case cbound c C hb =>
    have hmap := ρ.cmap c (CBinding.bound (CBound.upper C)) hb
    simpa [CaptureSet.crename, CBinding.crename, CBound.crename] using Subcapt.cbound hmap

/-! ## `Subbound` is preserved under capture variable renaming -/

/--
Subbounding is preserved under capture variable renaming.
If `Γ ⊢ B1 <:b B2` and `ρ : CVarMap Γ f Δ`, then `Δ ⊢ B1.crename f <:b B2.crename f`.
-/
theorem Subbound.crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    (h : Subbound Γ B1 B2)
    (ρ : CVarMap Γ f Δ) :
    Subbound Δ (B1.crename f) (B2.crename f) := by
  cases h
  case set hc =>
    simp [CBound.crename]
    apply Subbound.set
    apply Subcapt.crename hc ρ
  case star =>
    simp [CBound.crename]
    apply Subbound.star

/-! ## Helper lemma for `CVarMap.tmap`

`CVarMap.tmap_crename` is a convenience lemma that allows using `ρ.tmap_crename hb`
instead of `ρ.tmap X tb hb` when the binding `tb` can be inferred from `hb`.
-/


/--
A capture variable renaming map `ρ : CVarMap Γ f Δ` lifts `Γ.TBound X tb` to
`Δ.TBound X (tb.crename f)`. This is a convenient shorthand for `ρ.tmap X tb hb`.
-/
lemma CVarMap.tmap_crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    {X : Fin m} {tb : TBinding n m k} (ρ : CVarMap Γ f Δ)
    (hb : Γ.TBound X tb) : Δ.TBound X (tb.crename f) :=
  ρ.tmap X tb hb

/-! ## `SSubtyp` is preserved under capture variable renaming -/

/--
`SSubtyp` is preserved under capture variable renaming.
If `Γ ⊢ S1 <:s S2` and `ρ : CVarMap Γ f Δ`, then `Δ ⊢ S1.crename f <:s S2.crename f`.

This is the main subtyping preservation theorem for shape types.
The proof uses mutual induction on the subtyping relation, simultaneously
proving preservation for `ESubtyp` and `CSubtyp`.
-/
theorem SSubtyp.crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    (h : SSubtyp Γ S1 S2)
    (ρ : CVarMap Γ f Δ) :
    SSubtyp Δ (S1.crename f) (S2.crename f) := by
  refine SSubtyp.rec
    (motive_1 := λ {n m k} Γm E1 E2 _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarMap Γm f' Δ'),
        ESubtyp Δ' (E1.crename f') (E2.crename f'))
    (motive_2 := λ {n m k} Γm C1 C2 _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarMap Γm f' Δ'),
        CSubtyp Δ' (C1.crename f') (C2.crename f'))
    (motive_3 := λ {n m k} Γm S1m S2m _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarMap Γm f' Δ'),
        SSubtyp Δ' (S1m.crename f') (S2m.crename f'))
    (fun {n m k Γm T1 T2 hC ih k' f' Δ' ρ'} => by
      simp [EType.crename]
      apply ESubtyp.exist
      apply ih (k' := k' + 1) f'.ext (Δ'.cvar (CBinding.bound CBound.star))
        (CVarMap.cext ρ' (CBinding.bound CBound.star)))
    (fun {n m k Γm T1 T2 hC ih k' f' Δ' ρ'} => by
      simp [EType.crename]
      apply ESubtyp.type
      apply ih f' Δ' ρ')
    (fun {n m k Γm C1 C2 S1m S2m hSc hS ih k' f' Δ' ρ'} => by
      simp [CType.crename]
      apply CSubtyp.capt
      · apply Subcapt.crename hSc ρ'
      · apply ih f' Δ' ρ')
    (fun {n m k Γm Sm k' f' Δ' ρ'} =>
      SSubtyp.top)
    (fun {n m k Γm Sm k' f' Δ' ρ'} =>
      SSubtyp.refl (S := Sm.crename f'))
    (fun {n m k Γm S1m S2m S3m h12 h23 ih12 ih23 k' f' Δ' ρ'} =>
      SSubtyp.trans (ih12 f' Δ' ρ') (ih23 f' Δ' ρ'))
    (fun {n m k Γm X Sm hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tvar
      simpa [TBinding.crename] using ρ'.tmap X (TBinding.bound Sm) hb)
    (fun {n m k Γm X Sm hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tinstl
      simpa [TBinding.crename] using ρ'.tmap X (TBinding.inst Sm) hb)
    (fun {n m k Γm X Sm hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tinstr
      simpa [TBinding.crename] using ρ'.tmap X (TBinding.inst Sm) hb)
    (fun {n m k Γm T1 T2 hc ih k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.boxed
      apply ih f' Δ' ρ')
    (fun {n m k Γm S2m S1m hs ih k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.label
      apply ih f' Δ' ρ')
    (fun {n m k Γm E2 E1 F1 F2 hc he ihc ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.xforall
      · apply ihc f' Δ' ρ'
      · apply ihe (k' := k') f' (Δ'.var (E2.crename f')) (CVarMap.ext ρ' E2))
    (fun {n m k Γm S2m S1m E1 E2 hs he ihs ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tforall
      · apply ihs f' Δ' ρ'
      · apply ihe (k' := k') f' (Δ'.tvar ((TBinding.bound S2m).crename f'))
          (CVarMap.text ρ' (TBinding.bound S2m)))
    (fun {n m k Γm B2 B1 E1 E2 hb he ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.cforall
      · apply Subbound.crename hb ρ'
      · apply ihe (k' := k' + 1) f'.ext (Δ'.cvar (CBinding.bound (B2.crename f')))
          (CVarMap.cext ρ' (CBinding.bound B2)))
    h f Δ ρ

/-! ## `CSubtyp` is preserved under capture variable renaming -/

/--
`CSubtyp` is preserved under capture variable renaming.
If `Γ ⊢ C1 <: C2` and `ρ : CVarMap Γ f Δ`, then `Δ ⊢ C1.crename f <: C2.crename f`.
-/
theorem CSubtyp.crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    (h : CSubtyp Γ C1 C2)
    (ρ : CVarMap Γ f Δ) :
    CSubtyp Δ (C1.crename f) (C2.crename f) := by
  cases h
  case capt hSc hS =>
    simp [CType.crename]
    apply CSubtyp.capt
    · apply Subcapt.crename hSc ρ
    · apply SSubtyp.crename hS ρ

/-! ## `ESubtyp` is preserved under capture variable renaming -/

/--
`ESubtyp` is preserved under capture variable renaming.
If `Γ ⊢ E1 <:e E2` and `ρ : CVarMap Γ f Δ`, then `Δ ⊢ E1.crename f <:e E2.crename f`.
-/
theorem ESubtyp.crename {Γ : Context n m k} {f : FinFun k k'} {Δ : Context n m k'}
    (h : ESubtyp Γ E1 E2)
    (ρ : CVarMap Γ f Δ) :
    ESubtyp Δ (E1.crename f) (E2.crename f) := by
  cases h
  case exist hC =>
    simp [EType.crename]
    apply ESubtyp.exist
    apply CSubtyp.crename hC (CVarMap.cext ρ (CBinding.bound CBound.star))
  case type hC =>
    simp [EType.crename]
    apply ESubtyp.type
    apply CSubtyp.crename hC ρ

/-! ## Term-Variable Renaming Preserves Subtyping

These theorems prove that subtyping relationships (`Subcapt`, `Subbound`,
`SSubtyp`, `CSubtyp`, `ESubtyp`) and capture set subset are preserved under
term-variable renaming via `VarMap` and `.rename`. They are the term-variable
analogs of the capture-variable `crename` lemmas above.
-/

/-! ### `CaptureSet.Subset` is preserved under term-variable renaming -/

/--
If `C1 ⊆ C2` as capture sets, then after renaming term variables with `f`,
we have `C1.rename f ⊆ C2.rename f`.
-/
theorem CaptureSet.Subset.rename {C1 C2 : CaptureSet n k}
    (h : C1 ⊆ C2) (f : FinFun n n') :
    C1.rename f ⊆ C2.rename f := by
  induction h with
  | empty => exact CaptureSet.Subset.empty
  | rfl => exact CaptureSet.Subset.rfl
  | union_l h1 h2 ih1 ih2 =>
      simp
      apply CaptureSet.Subset.union_l ih1 ih2
  | union_rl h ih =>
      simp
      apply CaptureSet.Subset.union_rl ih
  | union_rr h ih =>
      simp
      apply CaptureSet.Subset.union_rr ih

/-! ### `Subcapt` is preserved under term-variable renaming -/

/--
Subcapturing is preserved under term-variable renaming.
If `Γ ⊢ C1 <:c C2` and `ρ : VarMap Γ f Δ`, then `Δ ⊢ C1.rename f <:c C2.rename f`.
-/
theorem Subcapt.rename {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
    (h : Subcapt Γ C1 C2)
    (ρ : VarMap Γ f Δ) :
    Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans h1 h2 ih1 ih2 =>
    exact Subcapt.trans (ih1 ρ) (ih2 ρ)
  case subset h =>
    exact Subcapt.subset (CaptureSet.Subset.rename h f)
  case union h1 h2 ih1 ih2 =>
    simpa using Subcapt.union (ih1 ρ) (ih2 ρ)
  case var x C S hb =>
    exact Subcapt.var (ρ.map x (CType.capt C S) hb)
  case cinstl c C hb =>
    exact Subcapt.cinstl (ρ.cmap c (CBinding.inst C) hb)
  case cinstr c C hb =>
    exact Subcapt.cinstr (ρ.cmap c (CBinding.inst C) hb)
  case cbound c C hb =>
    exact Subcapt.cbound (ρ.cmap c (CBinding.bound (CBound.upper C)) hb)

/-! ### `Subbound` is preserved under term-variable renaming -/

/--
Subbounding is preserved under term-variable renaming.
If `Γ ⊢ B1 <:b B2` and `ρ : VarMap Γ f Δ`, then `Δ ⊢ B1.rename f <:b B2.rename f`.
-/
theorem Subbound.rename {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
    (h : Subbound Γ B1 B2)
    (ρ : VarMap Γ f Δ) :
    Subbound Δ (B1.rename f) (B2.rename f) := by
  cases h with
  | set h => exact Subbound.set (Subcapt.rename h ρ)
  | star => exact Subbound.star

/-! ### `SSubtyp` is preserved under term-variable renaming -/

/--
`SSubtyp` is preserved under term-variable renaming.
If `Γ ⊢ S1 <:s S2` and `ρ : VarMap Γ f Δ`, then `Δ ⊢ S1.rename f <:s S2.rename f`.

This is the main subtyping preservation theorem for shape types under term-variable
renaming. The proof uses mutual induction on the subtyping relation, simultaneously
proving preservation for `ESubtyp` and `CSubtyp`.
-/
theorem SSubtyp.rename {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
    (h : SSubtyp Γ S1 S2)
    (ρ : VarMap Γ f Δ) :
    SSubtyp Δ (S1.rename f) (S2.rename f) := by
  let rec local_S {n m k n' : Nat} {S1 S2 : SType n m k} {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
      (h : SSubtyp Γ S1 S2)
      (ρ : VarMap Γ f Δ) :
      SSubtyp Δ (S1.rename f) (S2.rename f) := by
    match h with
    | .top => exact .top
    | .refl => exact .refl
    | .trans h1 h2 => exact .trans (local_S h1 ρ) (local_S h2 ρ)
    | .tvar hb => exact .tvar (ρ.tmap _ _ hb)
    | .tinstl hb => exact .tinstl (ρ.tmap _ _ hb)
    | .tinstr hb => exact .tinstr (ρ.tmap _ _ hb)
    | .boxed h => exact .boxed (local_C h ρ)
    | .label h => exact .label (local_S h ρ)
    | .xforall hc he =>
      exact .xforall (local_C hc ρ) (local_E he (VarMap.ext ρ _))
    | .tforall hs he =>
      exact .tforall (local_S hs ρ) (local_E he (VarMap.text ρ _))
    | .cforall hb he =>
      exact .cforall (Subbound.rename hb ρ) (local_E he (VarMap.cext ρ _)),
  local_C {n m k n' : Nat} {C1 C2 : CType n m k} {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
      (h : CSubtyp Γ C1 C2)
      (ρ : VarMap Γ f Δ) :
      CSubtyp Δ (C1.rename f) (C2.rename f) := by
    match h with
    | .capt hc hs => exact .capt (Subcapt.rename hc ρ) (local_S hs ρ),
  local_E {n m k n' : Nat} {E1 E2 : EType n m k} {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
      (h : ESubtyp Γ E1 E2)
      (ρ : VarMap Γ f Δ) :
      ESubtyp Δ (E1.rename f) (E2.rename f) := by
    match h with
    | .exist h => exact .exist (local_C h (VarMap.cext ρ _))
    | .type h => exact .type (local_C h ρ)
  exact local_S h ρ

/-! ### `CSubtyp` is preserved under term-variable renaming -/

/--
`CSubtyp` is preserved under term-variable renaming.
If `Γ ⊢ C1 <: C2` and `ρ : VarMap Γ f Δ`, then `Δ ⊢ C1.rename f <: C2.rename f`.
-/
theorem CSubtyp.rename {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
    (h : CSubtyp Γ C1 C2)
    (ρ : VarMap Γ f Δ) :
    CSubtyp Δ (C1.rename f) (C2.rename f) := by
  match h with
  | .capt hc hs => exact .capt (Subcapt.rename hc ρ) (SSubtyp.rename hs ρ)

/-! ### `ESubtyp` is preserved under term-variable renaming -/

/--
`ESubtyp` is preserved under term-variable renaming.
If `Γ ⊢ E1 <:e E2` and `ρ : VarMap Γ f Δ`, then `Δ ⊢ E1.rename f <:e E2.rename f`.
-/
theorem ESubtyp.rename {Γ : Context n m k} {f : FinFun n n'} {Δ : Context n' m k}
    (h : ESubtyp Γ E1 E2)
    (ρ : VarMap Γ f Δ) :
    ESubtyp Δ (E1.rename f) (E2.rename f) := by
  match h with
  | .exist h => exact .exist (CSubtyp.rename h (VarMap.cext ρ _))
  | .type h => exact .type (CSubtyp.rename h ρ)

/-! ## Type-Variable Renaming Preserves Subtyping

These theorems prove that subtyping relationships (`Subcapt`, `Subbound`,
`SSubtyp`) are preserved under type-variable renaming via `TVarMap`.
They are the type-variable analogs of the term-variable `rename` and
capture-variable `crename` lemmas above.
-/

/-! ### `Subcapt` is preserved under type-variable renaming -/

/--
Subcapturing is preserved under type-variable renaming.
If `Γ ⊢ C1 <:c C2` and `ρ : TVarMap Γ f Δ`, then `Δ ⊢ C1 <:c C2`.
-/
theorem Subcapt.trename (h : Subcapt Γ C1 C2) (ρ : TVarMap Γ f Δ) :
    Subcapt Δ C1 C2 := by
  induction h with
  | trans h1 h2 ih1 ih2 => exact Subcapt.trans (ih1 ρ) (ih2 ρ)
  | subset h => exact Subcapt.subset h
  | union h1 h2 ih1 ih2 => exact Subcapt.union (ih1 ρ) (ih2 ρ)
  | var hb => exact Subcapt.var (ρ.map _ _ hb)
  | cinstl hb => exact Subcapt.cinstl (ρ.cmap _ _ hb)
  | cinstr hb => exact Subcapt.cinstr (ρ.cmap _ _ hb)
  | cbound hb => exact Subcapt.cbound (ρ.cmap _ _ hb)

/-! ### `Subbound` is preserved under type-variable renaming -/

/--
Subbounding is preserved under type-variable renaming.
If `Γ ⊢ B1 <:b B2` and `ρ : TVarMap Γ f Δ`, then `Δ ⊢ B1 <:b B2`.
-/
theorem Subbound.trename (h : Subbound Γ B1 B2) (ρ : TVarMap Γ f Δ) :
    Subbound Δ B1 B2 := by
  induction h with
  | set hsub => exact Subbound.set (Subcapt.trename hsub ρ)
  | star => exact Subbound.star

/-! ### `SSubtyp` is preserved under type-variable renaming -/

/--
`SSubtyp` is preserved under type-variable renaming.
If `Γ ⊢ S1 <:s S2` and `ρ : TVarMap Γ f Δ`, then `Δ ⊢ S1.trename f <:s S2.trename f`.

This is the main subtyping preservation theorem for shape types under type-variable
renaming. The proof uses mutual induction on the subtyping relation, simultaneously
proving preservation for `ESubtyp` and `CSubtyp`.
-/
theorem SSubtyp.trename
    (h : SSubtyp Γ S1 S2)
    (ρ : TVarMap Γ f Δ) :
    SSubtyp Δ (S1.trename f) (S2.trename f) := by
  let motive_ESubtyp {n m k : ℕ} (Γ : Context n m k) (E1 E2 : EType n m k)
    (_ : ESubtyp Γ E1 E2) : Prop :=
    ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
    ESubtyp Δ (E1.trename f) (E2.trename f)
  let motive_CSubtyp {n m k : ℕ} (Γ : Context n m k) (T1 T2 : CType n m k)
    (_ : CSubtyp Γ T1 T2) : Prop :=
    ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
    CSubtyp Δ (T1.trename f) (T2.trename f)
  let motive_SSubtyp {n m k : ℕ} (Γ : Context n m k) (S1 S2 : SType n m k)
    (_ : SSubtyp Γ S1 S2) : Prop :=
    ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
    SSubtyp Δ (S1.trename f) (S2.trename f)
  refine (SSubtyp.rec
    (motive_1 := motive_ESubtyp)
    (motive_2 := motive_CSubtyp)
    (motive_3 := motive_SSubtyp)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) h f Δ ρ
  · -- ESubtyp.exist
    intro n m k Γ' T1 T2 hc ih m' f' Δ' ρ'
    apply ESubtyp.exist
    apply ih f' (Δ'.cvar (CBinding.bound CBound.star))
    exact TVarMap.cext ρ' (CBinding.bound CBound.star)
  · -- ESubtyp.type
    intro n m k Γ' T1 T2 hc ih m' f' Δ' ρ'
    apply ESubtyp.type
    apply ih f' Δ' ρ'
  · -- CSubtyp.capt
    intro n m k Γ' C1 C2 S1' S2' hsubc hs ih m' f' Δ' ρ'
    apply CSubtyp.capt
    · exact Subcapt.trename hsubc ρ'
    · apply ih f' Δ' ρ'
  · -- SSubtyp.top
    intro n m k Γ' S' m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.top
  · -- SSubtyp.refl
    intro n m k Γ' S' m' f' Δ' ρ'
    apply SSubtyp.refl
  · -- SSubtyp.trans
    intro n m k Γ' S1' S2' S3' h12 h23 ih12 ih23 m' f' Δ' ρ'
    apply SSubtyp.trans
    · apply ih12 f' Δ' ρ'
    · apply ih23 f' Δ' ρ'
  · -- SSubtyp.tvar
    intro n m k Γ' X S' hb m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tvar
    exact ρ'.tmap X (TBinding.bound S') hb
  · -- SSubtyp.tinstl
    intro n m k Γ' X S' hb m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tinstl
    exact ρ'.tmap X (TBinding.inst S') hb
  · -- SSubtyp.tinstr
    intro n m k Γ' X S' hb m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tinstr
    exact ρ'.tmap X (TBinding.inst S') hb
  · -- SSubtyp.boxed
    intro n m k Γ' T1 T2 hc ih m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.boxed
    apply ih f' Δ' ρ'
  · -- SSubtyp.label
    intro n m k Γ' S2' S1' hs ih m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.label
    apply ih f' Δ' ρ'
  · -- SSubtyp.xforall
    intro n m k Γ' E2 E1 F1 F2 hc hes ihc ihes m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.xforall
    · apply ihc f' Δ' ρ'
    · apply ihes f' (Δ'.var (E2.trename f'))
      exact TVarMap.ext ρ' E2
  · -- SSubtyp.tforall
    intro n m k Γ' S2' S1' E1 E2 hs hes ihs ihes m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tforall
    · apply ihs f' Δ' ρ'
    · apply ihes (f'.ext) (Δ'.tvar (TBinding.bound (S2'.trename f')))
      exact TVarMap.text ρ' (TBinding.bound S2')
  · -- SSubtyp.cforall
    intro n m k Γ' B2 B1 E1 E2 hsub hes ihes m' f' Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.cforall
    · exact Subbound.trename hsub ρ'
    · apply ihes f' (Δ'.cvar (CBinding.bound B2))
      exact TVarMap.cext ρ' (CBinding.bound B2)

end Capless
