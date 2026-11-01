import Capless.Inversion.Subtyping
import verisoftbench.Capless.Subtyping.Basic
import verisoftbench.Capless.Inversion.Context

/-!
# Subtyping Inversion Lemmas

Inversion lemmas for the subtyping relation `SSubtyp` in System Capless, relating
dealised `SType.box` types through the `SSubtyp` judgment.
-/

namespace Capless

/-! ## Dealias determinism lemmas -/

/--
`SType.Dealias` is deterministic for label types: if `S` dealiases to both
`SType.label T1` and `SType.label T2`, then `T1 = T2`.
-/
lemma dealias_label_det {Γ : Context n m k} {S : SType n m k} {T1 T2 : SType n m k}
    (hd1 : SType.Dealias Γ S (SType.label T1))
    (hd2 : SType.Dealias Γ S (SType.label T2)) : T1 = T2 := by
  have dealias_terminal_det {n m k : Nat} {Γ : Context n m k} {S S1 S2 : SType n m k}
      (h1 : SType.Dealias Γ S S1) (h2 : SType.Dealias Γ S S2)
      (hn1 : ∀ X, S1 ≠ SType.tvar X) (hn2 : ∀ X, S2 ≠ SType.tvar X) : S1 = S2 := by
    induction h1 generalizing S2 with
    | refl =>
      cases h2 with
      | refl => rfl
      | step hb hd => exact False.elim (hn1 _ rfl)
    | step hb hd ih =>
      cases h2 with
      | refl => exact False.elim (hn2 _ rfl)
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ih hd' hn1 hn2
  have e := dealias_terminal_det hd1 hd2 (by intro X he; cases he) (by intro X he; cases he)
  cases e
  rfl

/-! ## Boxed subtyping inversion -/

/--
If `Γ.IsTight`, `S1` dealiases to `SType.box T1`, `S2` dealiases to `SType.box T2`,
and `S1 <:s S2`, then `T1 <: T2` (as `CSubtyp`).

This is an inversion lemma that extracts the inner `CSubtyp` judgment from a
subtyping relationship between dealised boxed types in a tight context.
-/
theorem SSubtyp.sub_dealias_boxed_inv_1
  (ht : Γ.IsTight)
  (h1 : SType.Dealias Γ S1 (SType.box T1))
  (h2 : SType.Dealias Γ S2 (SType.box T2))
  (hs : SSubtyp Γ S1 S2) :
  CSubtyp Γ T1 T2 := by
  have dealias_terminal_det {n m k : Nat} {Γ : Context n m k} {S S1 S2 : SType n m k}
      (h1 : SType.Dealias Γ S S1) (h2 : SType.Dealias Γ S S2)
      (hn1 : ∀ X, S1 ≠ SType.tvar X) (hn2 : ∀ X, S2 ≠ SType.tvar X) : S1 = S2 := by
    induction h1 generalizing S2 with
    | refl =>
      cases h2 with
      | refl => rfl
      | step hb hd => exact False.elim (hn1 _ rfl)
    | step hb hd ih =>
      cases h2 with
      | refl => exact False.elim (hn2 _ rfl)
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ih hd' hn1 hn2
  let rec sub_box_right {n m k : Nat} {Γ : Context n m k} {S1 S2 : SType n m k}
      (hs : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
      {T2} (hd : SType.Dealias Γ S2 (.box T2)) :
      ∃ T1, SType.Dealias Γ S1 (.box T1) ∧ CSubtyp Γ T1 T2 := by
    match hs with
    | .top => cases hd
    | .refl => exact ⟨_, hd, CSubtyp.refl _⟩
    | .trans h1 h2 =>
      obtain ⟨T, hT, hsub⟩ := sub_box_right h2 ht hd
      obtain ⟨T1, hd1, hsub1⟩ := sub_box_right h1 ht hT
      exact ⟨T1, hd1, CSubtyp.trans hsub1 hsub⟩
    | .tvar hb => exact False.elim (ht.no_tbound_bound hb)
    | .tinstl hb =>
      cases hd with
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ⟨_, hd', CSubtyp.refl _⟩
    | .tinstr hb => exact ⟨_, .step hb hd, CSubtyp.refl _⟩
    | .boxed h => cases hd; exact ⟨_, .refl, h⟩
    | .label _ => cases hd
    | .xforall _ _ => cases hd
    | .tforall _ _ => cases hd
    | .cforall _ _ => cases hd
  obtain ⟨T, hd, hsub⟩ := sub_box_right hs ht h2
  have e := dealias_terminal_det h1 hd (by intro X he; cases he) (by intro X he; cases he)
  cases e
  exact hsub

/-! ## Label subtyping inversion -/

/--
Label subtyping inversion in a tight context.

If `Γ.IsTight`, `S1` dealiases to `SType.label T1`, `S2` dealiases to `SType.label T2`,
and `S1 <:s S2`, then `T2 <:s T1` (note the contravariance: label subtyping flips the
direction of inner types).

The proof uses induction on `SSubtyp` via `SSubtyp.rec` with custom motives that
simultaneously track dealias compatibility. As with `sub_dealias_boxed_inv_1`, the
dependent pattern matching interacts fragilely with variable indices.
-/
theorem SSubtyp.sub_dealias_label_inv_1
  {n m k : Nat} {Γ : Context n m k} {S1 S2 T1 T2 : SType n m k}
  (ht : Γ.IsTight)
  (h1 : SType.Dealias Γ S1 (SType.label T1))
  (h2 : SType.Dealias Γ S2 (SType.label T2))
  (hs : SSubtyp Γ S1 S2) :
  SSubtyp Γ T2 T1 := by
  let rec sub_label_right {Γ : Context n m k} {S1 S2 : SType n m k}
      (hs : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
      {T2} (hd : SType.Dealias Γ S2 (.label T2)) :
      ∃ T1, SType.Dealias Γ S1 (.label T1) ∧ SSubtyp Γ T2 T1 := by
    match hs with
    | .top => cases hd
    | .refl => exact ⟨_, hd, .refl⟩
    | .trans h1 h2 =>
      obtain ⟨T, hT, hsub⟩ := sub_label_right h2 ht hd
      obtain ⟨T1, hd1, hsub1⟩ := sub_label_right h1 ht hT
      exact ⟨T1, hd1, .trans hsub hsub1⟩
    | .tvar hb => exact False.elim (ht.no_tbound_bound hb)
    | .tinstl hb =>
      cases hd with
      | step hb' hd' =>
        have e := Context.TBound.inst_unique hb hb'
        subst e
        exact ⟨_, hd', .refl⟩
    | .tinstr hb => exact ⟨_, .step hb hd, .refl⟩
    | .boxed _ => cases hd
    | .label h => cases hd; exact ⟨_, .refl, h⟩
    | .xforall _ _ => cases hd
    | .tforall _ _ => cases hd
    | .cforall _ _ => cases hd
  obtain ⟨T, hd, hsub⟩ := sub_label_right hs ht h2
  have e := dealias_label_det h1 hd
  cases e
  exact hsub

end Capless
