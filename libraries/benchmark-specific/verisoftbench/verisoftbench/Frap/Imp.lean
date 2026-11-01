import Frap.Exercises.Trans

/-!
# Imp Language Behavioral Equivalence Congruence and Optimization Soundness

Theorems from Software Foundations' _Programming Language Foundations_ (the Imp
imperative language chapter).  Includes congruence lemmas for command equivalence
(`cequiv`) and soundness proofs for the `optimize_0plus` family of transformations.
-/

set_option quotPrecheck false

namespace Imp
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

/-! ### Soundness of the `optimize_0plus` family -/

/--
The `optimize_0plus_aexp` transformation (which simplifies `0 + e` to `e`) is sound:
it preserves arithmetic expression equivalence.
-/
theorem optimize_0plus_aexp_sound' : atrans_sound optimize_0plus_aexp := by
  intro a st
  induction a with
  | a_num n => simp [optimize_0plus_aexp]
  | a_id x => simp [optimize_0plus_aexp]
  | a_plus a1 a2 ih1 ih2 =>
    cases a1 with
    | a_num n =>
      cases n with
      | zero => simp [optimize_0plus_aexp, ih2]
      | succ n => simp [optimize_0plus_aexp, ih2]
    | a_id x => simp [optimize_0plus_aexp, ih2]
    | a_plus a1' a2' =>
      simp [optimize_0plus_aexp, aeval]
      rw [ih2]
      simpa [aeval] using ih1
    | a_minus a1' a2' =>
      simp [optimize_0plus_aexp, aeval]
      rw [ih2]
      simpa [aeval] using ih1
    | a_mult a1' a2' =>
      simp [optimize_0plus_aexp, aeval]
      rw [ih2]
      simpa [aeval] using ih1
  | a_minus a1 a2 ih1 ih2 =>
    simp [optimize_0plus_aexp, ih1, ih2]
  | a_mult a1 a2 ih1 ih2 =>
    simp [optimize_0plus_aexp, ih1, ih2]

/--
The `optimize_0plus_bexp` transformation is sound:
it preserves boolean expression equivalence.
-/
theorem optimize_0plus_bexp_sound' : btrans_sound optimize_0plus_bexp := by
  intro b st
  induction b with
  | b_true => simp [optimize_0plus_bexp]
  | b_false => simp [optimize_0plus_bexp]
  | b_eq a1 a2 =>
    have ha1 := optimize_0plus_aexp_sound' a1 st
    have ha2 := optimize_0plus_aexp_sound' a2 st
    simp [optimize_0plus_bexp, ha1, ha2]
  | b_neq a1 a2 =>
    have ha1 := optimize_0plus_aexp_sound' a1 st
    have ha2 := optimize_0plus_aexp_sound' a2 st
    simp [optimize_0plus_bexp, ha1, ha2]
  | b_le a1 a2 =>
    have ha1 := optimize_0plus_aexp_sound' a1 st
    have ha2 := optimize_0plus_aexp_sound' a2 st
    simp [optimize_0plus_bexp, ha1, ha2]
  | b_not b1 ih =>
    simp [optimize_0plus_bexp, ih]
  | b_and b1 b2 ih1 ih2 =>
    simp [optimize_0plus_bexp, ih1, ih2]
  | b_or b1 b2 ih1 ih2 =>
    simp [optimize_0plus_bexp, ih1, ih2]

/-! ### Congruence lemmas for `cequiv` -/

/--
Congruence of `cequiv` for assignment: if `a` and `a'` are equivalent,
then `x := a` and `x := a'` are equivalent.
-/
theorem casgn_cequiv {x : String} {a a' : AExp} (ha : aequiv a a') :
    cequiv (c_asgn x a) (c_asgn x a') := by
  intro st st'
  constructor
  · intro h
    cases h
    rename_i haev
    apply e_asgn
    rw [← ha st, haev]
  · intro h
    cases h
    rename_i haev
    apply e_asgn
    rw [ha st, haev]

/--
Congruence of `cequiv` for sequential composition.
-/
theorem cseq_cequiv {c1 c2 c1' c2' : Com} (h1 : cequiv c1 c1') (h2 : cequiv c2 c2') :
    cequiv (c_seq c1 c2) (c_seq c1' c2') := by
  intro st st'
  constructor
  · intro h
    cases h
    rename_i stmid hc1 hc2
    apply e_seq
    · exact ((h1 st stmid).mp hc1)
    · exact ((h2 stmid st').mp hc2)
  · intro h
    cases h
    rename_i stmid hc1 hc2
    apply e_seq
    · exact ((h1 st stmid).mpr hc1)
    · exact ((h2 stmid st').mpr hc2)

/--
Congruence of `cequiv` for conditional (if-then-else).
-/
theorem cif_cequiv {b b' : BExp} {c1 c2 c1' c2' : Com}
    (hb : bequiv b b') (h1 : cequiv c1 c1') (h2 : cequiv c2 c2') :
    cequiv (c_if b c1 c2) (c_if b' c1' c2') := by
  intro st st'
  constructor
  · intro h
    cases h
    · rename_i hbeval hc
      apply e_ifTrue
      · rw [← hb st, hbeval]
      · exact ((h1 st st').mp hc)
    · rename_i hbeval hc
      apply e_ifFalse
      · rw [← hb st, hbeval]
      · exact ((h2 st st').mp hc)
  · intro h
    cases h
    · rename_i hbeval hc
      apply e_ifTrue
      · rw [hb st, hbeval]
      · exact ((h1 st st').mpr hc)
    · rename_i hbeval hc
      apply e_ifFalse
      · rw [hb st, hbeval]
      · exact ((h2 st st').mpr hc)

/--
Congruence of `cequiv` for while loops.
-/
theorem cwhile_cequiv {b b' : BExp} {c c' : Com}
    (hb : bequiv b b') (hc : cequiv c c') :
    cequiv (c_while b c) (c_while b' c') := by
  intro st st'
  constructor
  · intro h
    generalize heq : c_while b c = com at h
    induction h with
    | e_whileFalse b1 c1 st0 hbf =>
      cases heq
      apply e_whileFalse
      rw [← hb st0, hbf]
    | e_whileTrue b1 c1 st0 st1 st2 hbf hcbody hwhile _ ihwhile2 =>
      cases heq
      apply e_whileTrue (b := b') (c := c') (st := st0) (st' := st1) (st'' := st2)
      · rw [← hb st0, hbf]
      · exact ((hc st0 st1).mp hcbody)
      · apply ihwhile2; rfl
    | e_skip => injection heq
    | e_asgn _ _ _ _ _ => injection heq
    | e_seq _ _ _ _ _ _ _ => injection heq
    | e_ifTrue _ _ _ _ _ _ _ => injection heq
    | e_ifFalse _ _ _ _ _ _ _ => injection heq
  · intro h
    generalize heq : c_while b' c' = com at h
    induction h with
    | e_whileFalse b1 c1 st0 hbf =>
      cases heq
      apply e_whileFalse
      rw [hb st0, hbf]
    | e_whileTrue b1 c1 st0 st1 st2 hbf hcbody hwhile _ ihwhile2 =>
      cases heq
      apply e_whileTrue (b := b) (c := c) (st := st0) (st' := st1) (st'' := st2)
      · rw [hb st0, hbf]
      · exact ((hc st0 st1).mpr hcbody)
      · apply ihwhile2; rfl
    | e_skip => injection heq
    | e_asgn _ _ _ _ _ => injection heq
    | e_seq _ _ _ _ _ _ _ => injection heq
    | e_ifTrue _ _ _ _ _ _ _ => injection heq
    | e_ifFalse _ _ _ _ _ _ _ => injection heq

/--
The `optimize_0plus_com` command transformer is sound:
it preserves command behavioral equivalence.
-/
theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com := by
  unfold ctrans_sound
  intro c
  induction c with
  | c_skip =>
    simp [optimize_0plus_com]
  | c_asgn x a =>
    have ha := optimize_0plus_aexp_sound' a
    simp [optimize_0plus_com]
    exact casgn_cequiv ha
  | c_seq c1 c2 ih1 ih2 =>
    simp [optimize_0plus_com]
    exact cseq_cequiv ih1 ih2
  | c_if b c1 c2 ih1 ih2 =>
    have hb := optimize_0plus_bexp_sound' b
    simp [optimize_0plus_com]
    exact cif_cequiv hb ih1 ih2
  | c_while b c ih =>
    have hb := optimize_0plus_bexp_sound' b
    simp [optimize_0plus_com]
    exact cwhile_cequiv hb ih

end Imp
