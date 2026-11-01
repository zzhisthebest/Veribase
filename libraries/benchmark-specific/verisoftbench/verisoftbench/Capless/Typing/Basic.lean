import Capless.Typing
import verisoftbench.Capless.Subst.Typing
import verisoftbench.Capless.Inversion.Context
import Capless.Inversion.Subtyping
import Capless.Inversion.Typing
import verisoftbench.Capless.Subtyping.Basic

/-!
# Basic Properties of Typing

Useful lemmas about the `Typed` relation of System Capless, including subsumption
variants (capture-only and type-only) and inversion of let-bindings.
-/

namespace Capless

/-! ## Context properties -/

/--
A variable cannot simultaneously have a `Bound` and an `LBound` in the same context.
-/
lemma bound_lbound_contra {Γ : Context n m k} {x : Fin n} {T : CType n m k} {S : SType n m k}
    (hb : Γ.Bound x T) (hl : Γ.LBound x S) : False := by
  induction hl
  case here =>
    cases hb
  case there_var hl' ih =>
    rcases Context.var_bound_succ_inv hb with ⟨T', hb', hT⟩
    exact ih hb'
  case there_tvar hl' ih =>
    cases hb
    case there_tvar hb' => exact ih hb'
  case there_cvar hl' ih =>
    cases hb
    case there_cvar hb' => exact ih hb'
  case there_label hl' ih =>
    rcases Context.label_bound_succ_inv hb with ⟨T', hb', hT⟩
    exact ih hb'

/-! ## Subsumption variants -/

/--
Subsumption via subcapturing only: if `Γ ⊢ t : E @ C1` and `Γ ⊢ C1 <:c C2`,
then `Γ ⊢ t : E @ C2`.
-/
lemma Typed.sub_capt {t : Term n m k} {E : EType n m k} {C1 C2 : CaptureSet n k}
    (h : Typed Γ t E C1) (hsc : Subcapt Γ C1 C2) : Typed Γ t E C2 :=
  Typed.sub h hsc (ESubtyp.refl E)

/--
Subsumption via subtyping only: if `Γ ⊢ t : E1 @ C` and `Γ ⊢ E1 <:e E2`,
then `Γ ⊢ t : E2 @ C`.
-/
lemma Typed.sub_type {t : Term n m k} {E1 E2 : EType n m k} {C : CaptureSet n k}
    (h : Typed Γ t E1 C) (hse : ESubtyp Γ E1 E2) : Typed Γ t E2 C :=
  Typed.sub h (Subcapt.refl C) hse

/-! ## Inversion of let-bindings -/

/--
Inversion lemma for `Term.letex`: breaks down a typing of `let (c,x)=t in u`
into typing of `t` with existential type and typing of `u` in an extended context.
The result is an existential giving the captured type `T` and the result type `E0`.
-/
theorem Typed.letex_inv'_1 {Γ : Context n m k}
  (he : t0 = Term.letex t u)
  (h : Typed Γ t0 E Ct0) :
  ∃ T E0,
    Typed Γ t (EType.ex T) Ct0 ∧
    Typed ((Γ.cvar (CBinding.bound CBound.star)).var T) u E0.cweaken.weaken Ct0.cweaken.weaken ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case letex =>
    cases he
    repeat apply Exists.intro
    constructor; assumption
    constructor; assumption
    apply ESubtyp.refl
  case sub hsc hs ih =>
    have ih := ih he
    obtain ⟨T, E0, ht, hu, hse0⟩ := ih
    have hse1 := ESubtyp.trans hse0 hs
    exact ⟨T, E0, Typed.sub_capt ht hsc, Typed.sub_capt hu (Subcapt.cweaken_weaken hsc), hse1⟩

/-! ## Variable inversion lemmas -/

/--
Inversion lemma for variable typing (primed version with explicit equality hypotheses):
if a variable `x` is typed with `EType.type T` in context `Γ` and is also bound in `Γ`
with some type `T0`, then there exists a capture set `C0` and shape type `S0` such that
`x` is bound with `S0^C0` and `S0^{x=x}` is a subtype of `T`.
-/
theorem Typed.var_inv'
    (he1 : t0 = Term.var x)
    (he2 : E0 = EType.type T)
    (h : Typed Γ t0 E0 Ct0) (hb : Γ.Bound x T0) :
    ∃ C0 S0, Γ.Bound x (S0^C0) ∧ (Γ ⊢ (S0^{x=x}) <: T) := by
  subst he1 he2
  generalize hterm : Term.var x = term_var
  generalize htype : EType.type T = etype
  have h' : Typed Γ term_var etype Ct0 := by
    subst hterm htype; exact h
  induction h' with
  | var hb' =>
    rename_i S_wild C_wild
    rcases (Term.var.inj hterm) with hx
    subst hx
    rcases (EType.type.inj htype) with hT
    subst hT
    refine ⟨S_wild, C_wild, hb', ?_⟩
    apply CSubtyp.capt
    · apply Subcapt.subset; exact CaptureSet.Subset.rfl
    · exact SSubtyp.refl
  | label hl =>
    rcases (Term.var.inj hterm) with hx
    subst hx
    exfalso; exact bound_lbound_contra hb hl
  | pack h1 => injection hterm
  | sub h1 h2 h3 ih =>
    rw [← hterm] at h1
    rw [← htype] at h3
    cases h3
    case type h_csub =>
      have h_rec := ih hb h1 hterm rfl
      rcases h_rec with ⟨c0, s0, hb0, h_sub⟩
      refine ⟨c0, s0, hb0, ?_⟩
      exact CSubtyp.trans h_sub h_csub
  | abs h1 => injection hterm
  | tabs h1 => injection hterm
  | cabs h1 => injection hterm
  | app h1 h2 => injection hterm
  | invoke h1 h2 => injection hterm
  | tapp h1 => injection hterm
  | capp h1 => injection hterm
  | letin h1 h2 => injection hterm
  | letex h1 h2 => injection hterm
  | bindt h1 => injection hterm
  | bindc h1 => injection hterm
  | boundary h1 => injection hterm

/-! ## Subcapture inversion lemmas -/

/--
Inversion lemma for variable subcapturing from typing.
If a variable `x` is typed with a concrete captured type `S^C`,
then the singleton capture set `{x=x}` is a subcapture of `C`.
This is a version with explicit equality hypotheses suitable for rewriting.
-/
theorem Typed.var_subcapt_inv'
    (he1 : t0 = Term.var x) (he2 : E0 = EType.type (CType.capt C S))
    (h : Typed Γ t0 E0 C0) :
    Subcapt Γ {x=x} C := by
  induction h with
  | var hbound =>
    cases he1
    cases he2
    exact Subcapt.refl _
  | label hbound =>
    cases he1
    cases he2
    exact Subcapt.refl _
  | sub hty hc hsub ih =>
    cases he1
    cases he2
    rcases ESubtyp.type_inv hsub with ⟨T', hE1, hcsub⟩
    rcases CSubtyp.capt_inv_right hcsub with ⟨C', S', hT1, hc', hs'⟩
    apply Subcapt.trans ?_ hc'
    apply ih rfl
    exact hE1.trans (congrArg EType.type hT1)
  | pack h => injection he1
  | abs h => injection he1
  | tabs h => injection he1
  | cabs h => injection he1
  | app hx hy => injection he1
  | invoke hx hy => injection he1
  | tapp hx => injection he1
  | capp hx => injection he1
  | letin ht hu => injection he1
  | letex ht hu => injection he1
  | bindt h => injection he1
  | bindc h => injection he1
  | boundary h => injection he1

/-! ## Type-application inversion lemmas -/

/--
Inversion lemma for type application: if `t0 = tapp x X` is typed with result type `E`,
then variable `x` must be typed with a universally quantified type `∀[X<:X]F^Cf`,
and the result type is `F.topen X` up to subtyping.
-/
theorem Typed.tapp_inv'_1
    (he : t0 = Term.tapp x X)
    (h : Typed Γ t0 E Ct) :
    ∃ Cf F E0,
      Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.tforall (SType.tvar X) F))) {x=x}
      ∧ E0 = F.topen X
      ∧ ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case tapp =>
    cases he
    repeat (apply Exists.intro)
    refine ⟨?_, rfl, ESubtyp.refl _⟩
    assumption
  case sub hs ih =>
    rcases ih he with ⟨Cf, F, E0, hx, he0, hs0⟩
    exact ⟨Cf, F, E0, hx, he0, ESubtyp.trans hs0 hs⟩

/-! ## Capture-application inversion lemmas -/

/--
Inversion lemma for capture application: if `t0 = capp x c` is typed with result type `E`,
then variable `x` must be typed with a universally quantified capture type `∀[c<:c]F^Cf`,
and the result type is `F.copen c` up to subtyping.
-/
theorem Typed.capp_inv'_1
    (he : t0 = Term.capp x c)
    (h : Typed Γ t0 E Ct) :
    ∃ Cf F E0,
      Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.cforall (CBound.upper {c=c}) F))) {x=x} ∧
      E0 = F.copen c ∧
      ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case capp =>
    cases he
    repeat (apply Exists.intro)
    refine ⟨by trivial, ?_⟩
    refine ⟨rfl, ?_⟩
    apply ESubtyp.refl
  case sub hs ih =>
    have ih := ih he
    rcases ih with ⟨Cf, F, E0, hx, he0, hs0⟩
    have h := ESubtyp.trans hs0 hs
    exact ⟨Cf, F, E0, hx, he0, h⟩

/-! ## Boundary inversion lemmas -/

/--
Inversion lemma for boundary typing: if `t0 = boundary:S in t` is typed in context `Γ`
with result type `E` and capture set `Ct`, then `t` is typed under the extended context
`(Γ,c<:*),x: Label[S.cweaken]^{c=0}` with result type `S.cweaken.weaken^{}` and capture set
`Ct.cweaken.weaken ∪ {c=0} ∪ {x=0}`, and `S^{}` is a subtype of `E`.
-/
theorem Typed.boundary_inv'_1 {Γ : Context n m k} {S : SType n m k}
    (he : t0 = (boundary:S in t))
    (ht : Typed Γ t0 E Ct) :
    Typed
      ((Γ.cvar (CBinding.bound CBound.star)).var (Label[S.cweaken]^{c=0}))
      t
      ((S.cweaken.weaken)^{})
      (Ct.cweaken.weaken ∪ {c=0} ∪ {x=0}) ∧
      (ESubtyp Γ ((S)^{}) E) := by
  induction ht with
  | sub hsub hc he_sub ih =>
    rcases ih he with ⟨h_t, h_e⟩
    constructor
    · apply Typed.sub h_t
      · let h_cww := Subcapt.cweaken_weaken (B := CBinding.bound CBound.star)
          (T := Label[S.cweaken]^{c=0}) hc
        apply Subcapt.union
        · apply Subcapt.union
          · apply Subcapt.trans h_cww
            apply Subcapt.subset
            apply CaptureSet.Subset.union_rl
            apply CaptureSet.Subset.union_rl
            exact CaptureSet.Subset.rfl
          · apply Subcapt.subset
            apply CaptureSet.Subset.union_rl
            apply CaptureSet.Subset.union_rr
            exact CaptureSet.Subset.rfl
        · apply Subcapt.subset
          apply CaptureSet.Subset.union_rr
          exact CaptureSet.Subset.rfl
      · apply ESubtyp.refl
    · exact ESubtyp.trans h_e he_sub
  | boundary hbody =>
    cases he
    constructor
    · exact hbody
    · apply ESubtyp.refl
  | var hx =>
    injection he
  | label hx =>
    injection he
  | pack hx =>
    injection he
  | abs hx =>
    injection he
  | tabs hx =>
    injection he
  | cabs hx =>
    injection he
  | app hx hy =>
    injection he
  | invoke hx hy =>
    injection he
  | tapp hx =>
    injection he
  | capp hx =>
    injection he
  | letin hx hy =>
    injection he
  | letex hx hy =>
    injection he
  | bindt hx =>
    injection he
  | bindc hx =>
    injection he

/-! ## Canonical form lemmas for lambda abstractions -/

/--
Canonical form lemma for lambda abstractions: in a tight context, if a lambda `Term.lam T t`
has a forall type `(∀(x:T')E)^Cf` (after dealiasing), then `T'` is a subtype of `T`,
and the body `t` has type `E` in the extended context `Γ.var T'` with a weakened capture set.

This is the primed version with dealiasing and explicit equality hypotheses.
-/
theorem Typed.canonical_form_lam'
  (ht : Γ.IsTight)
  (he1 : t0 = Term.lam T t) (hd2 : SType.Dealias Γ S0 (SType.forall T' E))
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct0) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E (Cf.weaken ∪ {x=0}) := by
  have capture_rename_id {n k : Nat} (C : CaptureSet n k) : C.rename FinFun.id = C := by
    induction C <;> simp_all [CaptureSet.rename, FinFun.id]

  have bound_rename_id {n k : Nat} (B : CBound n k) : B.rename FinFun.id = B := by
    cases B <;> simp [CBound.rename, capture_rename_id]

  let rec effect_rename_id {n m k : Nat} (E : EType n m k) : E.rename FinFun.id = E :=
    match E with
    | .ex T => by simp [EType.rename, ctype_rename_id T]
    | .type T => by simp [EType.rename, ctype_rename_id T],
  ctype_rename_id {n m k : Nat} (T : CType n m k) : T.rename FinFun.id = T :=
    match T with
    | .capt C S => by simp [CType.rename, capture_rename_id, stype_rename_id S],
  stype_rename_id {n m k : Nat} (S : SType n m k) : S.rename FinFun.id = S :=
    match S with
    | .top => rfl
    | .tvar _ => rfl
    | .forall T E => by simp [SType.rename, FinFun.id_ext, ctype_rename_id T, effect_rename_id E]
    | .tforall S E => by simp [SType.rename, stype_rename_id S, effect_rename_id E]
    | .cforall B E => by simp [SType.rename, bound_rename_id, effect_rename_id E]
    | .box T => by simp [SType.rename, ctype_rename_id T]
    | .label S => by simp [SType.rename, stype_rename_id S]

  have term_rename_id {n m k : Nat} (t : Term n m k) : t.rename FinFun.id = t := by
    induction t <;> simp_all [Term.rename, ctype_rename_id, stype_rename_id,
      bound_rename_id, capture_rename_id, FinFun.id_ext, FinFun.id]

  have term_crename_id {n m k : Nat} (t : Term n m k) : t.crename FinFun.id = t := by
    induction t <;> simp_all [Term.crename, CType.crename_id, SType.crename_id,
      CBound.crename_id, CaptureSet.crename_id, FinFun.id_ext, FinFun.id]
  have effect_subst {n m k n' : Nat} {Γ : Context n m k} {Δ : Context n' m k}
      {f : FinFun n n'} {E1 E2 : EType n m k}
      (h : ESubtyp Γ E1 E2) (σ : VarSubst Γ f Δ) :
      ESubtyp Δ (E1.rename f) (E2.rename f) := by
    cases h with
    | exist h =>
      cases h with
      | capt hc hs => exact .exist (.capt (Subcapt.subst hc σ.cext) (SSubtyp.subst hs σ.cext))
    | type h =>
      cases h with
      | capt hc hs => exact .type (.capt (Subcapt.subst hc σ) (SSubtyp.subst hs σ))
  let rec forall_right {n m k : Nat} {T2 : CType n m k} {E2 : EType (n+1) m k} {Γ : Context n m k} {S1 S2 : SType n m k}
      (hs : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
      (hd : SType.Dealias Γ S2 (.forall T2 E2)) :
      ∃ T1 E1, SType.Dealias Γ S1 (.forall T1 E1) ∧
        CSubtyp Γ T2 T1 ∧ ESubtyp (Γ.var T2) E1 E2 := by
    match hs with
    | .top => cases hd
    | .refl => exact ⟨_, _, hd, CSubtyp.refl _, ESubtyp.refl _⟩
    | .trans h1 h2 =>
      obtain ⟨Tm, Em, hdm, htm, hem⟩ := forall_right h2 ht hd
      obtain ⟨T1, E1, hd1, ht1, he1⟩ := forall_right h1 ht hdm
      have he1' := effect_subst he1 (VarSubst.narrow htm)
      exact ⟨_, _, hd1, CSubtyp.trans htm ht1,
        ESubtyp.trans (by simpa [effect_rename_id] using he1') hem⟩
    | .tvar hb => exact False.elim (ht.no_tbound_bound hb)
    | .tinstl hb =>
      cases hd with
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ⟨_, _, hd', CSubtyp.refl _, ESubtyp.refl _⟩
    | .tinstr hb => exact ⟨_, _, .step hb hd, CSubtyp.refl _, ESubtyp.refl _⟩
    | .xforall hc he => cases hd; exact ⟨_, _, .refl, hc, he⟩
    | .boxed _ => cases hd
    | .label _ => cases hd
    | .tforall _ _ => cases hd
    | .cforall _ _ => cases hd
  induction h with
  | abs hb =>
    cases he1; cases he2; cases hd2
    exact ⟨CSubtyp.refl _, hb⟩
  | sub h hc hs ih =>
    cases hs with
    | exist hs => cases he2
    | type hs =>
      cases hs with
      | capt hcap hs =>
        cases he2
        obtain ⟨Tm, Em, hdm, htm, hem⟩ := forall_right hs ht hd2
        obtain ⟨hdom, hb⟩ := ih ht he1 hdm rfl
        have hb' := Typed.subst_1 hb (VarSubst.narrow htm)
        simp only [term_rename_id,
          effect_rename_id, capture_rename_id] at hb'
        refine ⟨CSubtyp.trans htm hdom, Typed.sub hb' ?_ hem⟩
        apply Subcapt.union
        · exact Subcapt.trans (Subcapt.weaken hcap) (.subset (.union_rl .rfl))
        · exact .subset (.union_rr .rfl)
  | _ => cases he1

/--
Canonical form lemma for capture lambda abstractions: in a tight context, if a capture lambda
`Term.clam B t` has a cforall type `∀[c<:B']E` (after dealiasing), then `B'` is a subbound of `B`,
and the body `t` has type `E` in the context extended with capture binding `B'`, with a
capture-weakened capture set `Cf.cweaken`.

This is the primed version with dealiasing and explicit equality hypotheses.
-/
theorem Typed.canonical_form_clam'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.cforall B' E))
  (he1 : t0 = Term.clam B t)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct0) :
  Subbound Γ B' B ∧ Typed (Γ.cvar (CBinding.bound B')) t E Cf.cweaken := by
  have term_crename_id {n m k : Nat} (t : Term n m k) : t.crename FinFun.id = t := by
    induction t <;> simp_all [Term.crename, CType.crename_id, SType.crename_id,
      CBound.crename_id, CaptureSet.crename_id, FinFun.id_ext, FinFun.id]
  have bound_refl {n m k : Nat} {Γ : Context n m k} (B : CBound n k) : Subbound Γ B B := by
    cases B with
    | upper C => exact .set (.subset .rfl)
    | star => exact .star

  have bound_trans {n m k : Nat} {Γ : Context n m k} {B1 B2 B3 : CBound n k} (h1 : Subbound Γ B1 B2) (h2 : Subbound Γ B2 B3) :
      Subbound Γ B1 B3 := by
    cases h2 with
    | star => exact .star
    | set h2 => cases h1 with | set h1 => exact .set (.trans h1 h2)
  let rec cforall_right {n m k : Nat} {B2 : CBound n k} {E2 : EType n m (k+1)} {Γ : Context n m k} {S1 S2 : SType n m k}
      (hs : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
      (hd : SType.Dealias Γ S2 (.cforall B2 E2)) :
      ∃ B1 E1, SType.Dealias Γ S1 (.cforall B1 E1) ∧
        Subbound Γ B2 B1 ∧ ESubtyp (Γ.cvar (.bound B2)) E1 E2 := by
    match hs with
    | .top => cases hd
    | .refl => exact ⟨_, _, hd, bound_refl _, ESubtyp.refl _⟩
    | .trans h1 h2 =>
      obtain ⟨Bm, Em, hdm, hbm, hem⟩ := cforall_right h2 ht hd
      obtain ⟨B1, E1, hd1, hb1, he1⟩ := cforall_right h1 ht hdm
      have he1' := ESubtyp.csubst he1 (CVarSubst.narrow hbm)
      exact ⟨_, _, hd1, bound_trans hbm hb1,
        ESubtyp.trans (by simpa [EType.crename_id] using he1') hem⟩
    | .tvar hb => exact False.elim (ht.no_tbound_bound hb)
    | .tinstl hb =>
      cases hd with
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ⟨_, _, hd', bound_refl _, ESubtyp.refl _⟩
    | .tinstr hb => exact ⟨_, _, .step hb hd, bound_refl _, ESubtyp.refl _⟩
    | .cforall hc he => cases hd; exact ⟨_, _, .refl, hc, he⟩
    | .boxed _ => cases hd
    | .label _ => cases hd
    | .tforall _ _ => cases hd
    | .xforall _ _ => cases hd
  induction h with
  | cabs hb =>
    cases he1; cases he2; cases hd
    constructor
    · exact bound_refl _
    · exact hb
  | sub h hc hs ih =>
    cases hs with
    | exist hs => cases he2
    | type hs =>
      cases hs with
      | capt hcap hs =>
        cases he2
        obtain ⟨Bm, Em, hdm, hbm, hem⟩ := cforall_right hs ht hd
        obtain ⟨hdom, hb⟩ := ih ht hdm he1 rfl
        have hb' := Typed.csubst_1 hb (CVarSubst.narrow hbm)
        simp only [term_crename_id,
          EType.crename_id, CaptureSet.crename_id] at hb'
        constructor
        · exact bound_trans hbm hdom
        · exact Typed.sub hb' (Subcapt.cweaken hcap) hem
  | _ => cases he1

/-! ## Pack inversion lemmas -/

/--
Canonical forms / inversion lemma for `Term.pack`: if a term `pack C x` is typed
with existential type `∃c.T` in a tight context `Γ`, then `x` has type `T`
in the context extended with capture binding `c := C`.
This is the inverse direction of the `Typed.pack` typing rule.
-/
theorem Typed.pack_inv' {Γ : Context n m k}
    (ht : Γ.IsTight)
    (he1 : t0 = Term.pack C x)
    (he2 : E0 = EType.ex T)
    (h : Typed Γ t0 E0 Ct) :
    Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) {x=x} := by
  induction h with
  | pack hx => cases he1; cases he2; exact hx
  | sub h hc hs ih =>
    cases hs with
    | type hs => cases he2
    | exist hs =>
      cases he2
      have hb := ih ht he1 rfl
      have hsub := CSubtyp.csubst hs (CVarSubst.instantiate (C := C))
      exact Typed.sub hb (.subset .rfl) (.type (by simpa [CType.crename_id] using hsub))
  | _ => cases he1

end Capless
