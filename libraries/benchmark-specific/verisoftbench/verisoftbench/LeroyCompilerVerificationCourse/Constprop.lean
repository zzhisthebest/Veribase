import LeroyCompilerVerificationCourse.Fixpoints
import verisoftbench.LeroyCompilerVerificationCourse.Fixpoints

open OrderStruct
open Monotone
open Std.HashMap

set_option quotPrecheck false

theorem join_left_upper_bound (S a : Store) : le S (Join S a) := by
  intro x n hm
  exact ((Join_characterization S a x n).mp hm).1

theorem join_right_upper_bound (S a : Store) : le a (Join S a) := by
  intro x n hm
  exact ((Join_characterization S a x n).mp hm).2

theorem join_left_small (S a z : Store) (h : le (Join S a) z) : le S z := by
  intro x n hm
  have h_join : (Join S a).get? x = some n := h x n hm
  exact ((Join_characterization S a x n).mp h_join).1

theorem join_right_small (S a z : Store) (h : le (Join S a) z) : le a z := by
  intro x n hm
  have h_join : (Join S a).get? x = some n := h x n hm
  exact ((Join_characterization S a x n).mp h_join).2

/-- Reflexivity of the `Le` relation on abstract stores. -/
theorem Le_refl (S : Store) : Le S S := by
  intro x n h; exact h

/-! ### Match relation and Join -/

/-- If a store matches `S1`, it also matches the join of `S1` with any `S2`. -/
theorem matches_Join_left (s : store) (S1 S2 : Store) (h : matches' s S1) :
    matches' s (Join S1 S2) := by
  intro x n hjoin
  have hleft := ((Join_characterization S1 S2 x n).mp hjoin).left
  exact h x n hleft

/-- If a store matches `S2`, it also matches the join of any `S1` with `S2`. -/
theorem matches_Join_right (s : store) (S1 S2 : Store) (h : matches' s S2) :
    matches' s (Join S1 S2) := by
  intro x n hjoin
  have hright := ((Join_characterization S1 S2 x n).mp hjoin).right
  exact h x n hright

theorem beq_eq_imp_le_right (a b : Store) (h : beq a b = true) : le b a := by
  have heq : Equal a b := beq_true' a b h
  have h_sym : Equal b a := Eq'_sym a b heq
  exact Eq_Le b a h_sym

theorem iterate_le_iterate_store {G1 G2 : Store → Store} [Monotone Store G1] [Monotone Store G2]
    (hG : ∀ z, le (G1 z) (G2 z))
    (x y : Store) (PRE1 : le x (G1 x)) (PRE2 : le y (G2 y))
    (SMALL1 : ∀ z, le (G1 z) z → le x z) (SMALL2 : ∀ z, le (G2 z) z → le y z) :
    le (iterate Store G1 x PRE1 SMALL1) (iterate Store G2 y PRE2 SMALL2) := by
  refine iterate.induct (α := Store) (F := G2)
    (motive := λ y' PRE2' SMALL2' =>
      le (iterate Store G1 x PRE1 SMALL1) (iterate Store G2 y' PRE2' SMALL2'))
    ?case1 ?case2 y PRE2 SMALL2
  · intro y' PRE2' SMALL2' h_eq
    rw [iterate.eq_1 (α := Store) (F := G2) (x := y') (PRE := PRE2') (SMALL := SMALL2')]
    rw [if_pos h_eq]
    have h_G1y_le_G2y : le (G1 y') (G2 y') := hG y'
    have h_G2y_le_y' : le (G2 y') y' := beq_eq_imp_le_right y' (G2 y') h_eq
    have h_G1y_le_y' : le (G1 y') y' :=
      Le_trans (G1 y') (G2 y') y' h_G1y_le_G2y h_G2y_le_y'
    exact iterate_le_of_postfix (G := G1) x y' PRE1 SMALL1 h_G1y_le_y'
  · intro y' PRE2' SMALL2' h_eq ih
    rw [iterate.eq_1 (α := Store) (F := G2) (x := y') (PRE := PRE2') (SMALL := SMALL2')]
    rw [if_neg h_eq]
    exact ih

/-! ### Boolean helper lemma -/

/-- If `beval s b` is not `true`, then it must be `false`. -/
theorem beval_eq_false_of_not_eq_true (s : store) (b : bexp) (h : ¬ beval s b = true) : beval s b = false := by
  match hb : beval s b with
  | true => exfalso; exact h hb
  | false => rfl

/-! ### Fixpoint soundness properties -/

/-- Auxiliary lemma: for any fuel `n` and initial store `S`,
  `F (fixpoint_rec F n S)` is below `fixpoint_rec F n S`. -/
theorem fixpoint_sound_aux (F : Store → Store) : ∀ (fuel : Nat) (S : Store), Le (F (fixpoint_rec F fuel S)) (fixpoint_rec F fuel S) := by
  intro fuel
  induction fuel with
  | zero =>
      intro S
      simp [fixpoint_rec, Le, Top]
  | succ fuel ih =>
      intro S
      simp [fixpoint_rec]
      by_cases h : Equal (F S) S
      · simp [h]
        have h_eq_gets : ∀ x, (F S).get? x = S.get? x := by
          intro x
          have := Std.HashMap.Equiv.getElem?_eq h (k := x)
          simpa using this
        unfold Le
        intro x n hget
        rw [h_eq_gets x]
        exact hget
      · simp [h]
        exact ih (F S)

/-- The fixpoint is a post-fixpoint: `F (fixpoint F init_S)` is below `fixpoint F init_S`. -/
theorem fixpoint_sound (F : Store → Store) (init_S : Store) : Le (F (fixpoint F init_S)) (fixpoint F init_S) :=
  fixpoint_sound_aux F num_iter init_S

/-- If `s` matches `S1`, then `s` also matches `fixpoint (fun x => Join S1 (Cexec x c)) S1`. -/
theorem fixpoint_matches (s : store) (S1 : Store) (c : com) (h : matches' s S1) : matches' s (fixpoint (fun x => Join S1 (Cexec x c)) S1) := by
  let F := fun x => Join S1 (Cexec x c)
  have hLe : Le (F (fixpoint F S1)) (fixpoint F S1) := fixpoint_sound F S1
  apply matches_Le s S1 (fixpoint F S1)
  · intro x n hx
    have hjoin := hLe x n hx
    rcases (Join_characterization S1 (Cexec (fixpoint F S1) c) x n).mp hjoin with ⟨hS1, _⟩
    exact hS1
  · exact h

/-- `Cexec (fixpoint ...)` applied to `c` is below the fixpoint. -/
theorem fixpoint_Le_Cexec (S1 : Store) (c : com) : Le (Cexec (fixpoint (fun x => Join S1 (Cexec x c)) S1) c) (fixpoint (fun x => Join S1 (Cexec x c)) S1) := by
  let sfix := fixpoint (fun x => Join S1 (Cexec x c)) S1
  let F := fun x => Join S1 (Cexec x c)
  have hLe : Le (F sfix) sfix := fixpoint_sound F S1
  intro x n hx
  have hjoin := hLe x n hx
  rcases (Join_characterization S1 (Cexec sfix c) x n).mp hjoin with ⟨_, hCex⟩
  exact hCex

/-! ### Updating abstract stores -/

/-- Updating a store with the evaluated value of an arithmetic expression
    preserves the matching relation, provided the abstract evaluation
    is sound.  Combines `matches_update` and `Aeval_sound`. -/
theorem matches_update_with_Aeval (s : store) (S1 : Store) (x : ident) (a : aexp)
    (h : matches' s S1) : matches' (update x (aeval s a) s) (Update x (Aeval S1 a) S1) := by
  apply matches_update s S1 x (aeval s a) (Aeval S1 a) h
  intro i hi
  exact Aeval_sound s S1 h a i hi

/-! ### Constant propagation correctness for loops -/

/-- Correctness of constant propagation for WHILE loops.
  Given a fixpoint store `sfix` with `Le (Cexec sfix c) sfix`,
  and a body correctness hypothesis, executing the propagated loop
  preserves the match and produces the propagated result. -/
theorem cp_while_correct (sfix : Store) (b : bexp) (c : com) (hfix : Le (Cexec sfix c) sfix)
    (h_body_correct : ∀ (st st' : store), cexec st c st' → matches' st sfix → (cexec st (cp_com sfix c) st' ∧ matches' st' (Cexec sfix c)))
    (st : store) (s2 : store) (hm_st : matches' st sfix) (h_exec : cexec st (.WHILE b c) s2) :
    (cexec st (mk_WHILE (cp_bexp sfix b) (cp_com sfix c)) s2 ∧ matches' s2 sfix) := by
  generalize hcmd : com.WHILE b c = cmd at h_exec
  induction h_exec generalizing sfix with
  | cexec_while_done hb' =>
    injection hcmd with hb_eq hc_eq
    subst hb_eq
    subst hc_eq
    constructor
    · apply cexec_mk_WHILE_done _ (cp_bexp sfix b) (cp_com sfix c)
      rw [cp_bexp_sound _ sfix hm_st b, hb']
    · exact hm_st
  | cexec_while_loop hb' hbody hrec'' ih_body ih_rec =>
    injection hcmd with hb_eq hc_eq
    subst hb_eq
    subst hc_eq
    rcases h_body_correct _ _ hbody hm_st with ⟨hcex_b, hm_b⟩
    have hm_st' : matches' _ sfix :=
      matches_Le _ (Cexec sfix c) sfix hfix hm_b
    have h_rec_res := ih_rec sfix hfix h_body_correct hm_st' rfl
    rcases h_rec_res with ⟨hcex_r, hm_st2⟩
    constructor
    · apply cexec_mk_WHILE_loop (cp_bexp sfix b) (cp_com sfix c) _ _ _ ?_ hcex_b hcex_r
      rw [cp_bexp_sound _ sfix hm_st b, hb']
    · exact hm_st2
  | cexec_skip => injection hcmd
  | cexec_assign => injection hcmd
  | cexec_seq => injection hcmd
  | cexec_ifthenelse => injection hcmd

/-! ### Main semantic preservation of constant propagation -/

/-- If `c` executes from `s1` to `s2` and `s1` matches abstract store `S1`,
  then `cp_com S1 c` also executes from `s1` to `s2` and `s2` matches `Cexec S1 c`. -/
theorem cp_com_correct_terminating_aux (c : com) (s1 s2 : store) (S1 : Store) (h1 : cexec s1 c s2) (h2 : matches' s1 S1) :
    (cexec s1 (cp_com S1 c) s2 ∧ matches' s2 (Cexec S1 c)) := by
  induction c generalizing s1 s2 S1 with
  | SKIP =>
    match h1 with
    | .cexec_skip =>
      constructor
      · exact .cexec_skip
      · exact h2
  | ASSIGN x a =>
    match h1 with
    | .cexec_assign =>
      have h_aeq : aeval s1 (cp_aexp S1 a) = aeval s1 a := cp_aexp_sound s1 S1 h2 a
      constructor
      · simp [cp_com]
        simpa [← h_aeq] using .cexec_assign (x := x) (a := cp_aexp S1 a) (s := s1)
      · simp [Cexec]
        apply matches_update s1 S1 x (aeval s1 a) (Aeval S1 a) h2
        intro i hi
        exact Aeval_sound s1 S1 h2 a i hi
  | SEQ c1 c2 ih1 ih2 =>
    match h1 with
    | .cexec_seq hc1 hc2 =>
      rcases ih1 s1 _ S1 hc1 h2 with ⟨hcex1, hm1⟩
      rcases ih2 _ s2 (Cexec S1 c1) hc2 hm1 with ⟨hcex2, hm2⟩
      constructor
      · simp [cp_com]
        exact .cexec_seq hcex1 hcex2
      · simp [Cexec]
        exact hm2
  | IFTHENELSE b c1 c2 ih1 ih2 =>
    match h1 with
    | .cexec_ifthenelse h =>
      by_cases hb : beval s1 b = true
      · have h_c1 : cexec s1 c1 s2 := by simpa [hb] using h
        rcases ih1 s1 s2 S1 h_c1 h2 with ⟨hcex, hm'⟩
        constructor
        · simp [cp_com]
          apply cexec_mk_IFTHENELSE s1 (cp_bexp S1 b) (cp_com S1 c1) (cp_com S1 c2) s2
          have hbeval' : beval s1 (cp_bexp S1 b) = true := by
            rw [cp_bexp_sound s1 S1 h2 b, hb]
          simpa [hbeval'] using hcex
        · simp [Cexec]
          cases hBeval : Beval S1 b
          · intro x n hjoin
            have hget := (Join_characterization (Cexec S1 c1) (Cexec S1 c2) x n).mp hjoin
            exact hm' x n hget.1
          · rename_i v
            have hbeval_s := Beval_sound s1 S1 h2 b v hBeval
            rw [hb] at hbeval_s
            cases v with
            | true => simpa [hBeval] using hm'
            | false => exact absurd hbeval_s (by decide : true ≠ false)
      · have hb_false : beval s1 b = false :=
          beval_eq_false_of_not_eq_true s1 b hb
        have h_c2 : cexec s1 c2 s2 := by simpa [hb_false] using h
        rcases ih2 s1 s2 S1 h_c2 h2 with ⟨hcex, hm'⟩
        constructor
        · simp [cp_com]
          apply cexec_mk_IFTHENELSE s1 (cp_bexp S1 b) (cp_com S1 c1) (cp_com S1 c2) s2
          have hbeval' : beval s1 (cp_bexp S1 b) = false := by
            rw [cp_bexp_sound s1 S1 h2 b, hb_false]
          simpa [hbeval'] using hcex
        · simp [Cexec]
          cases hBeval : Beval S1 b
          · intro x n hjoin
            have hget := (Join_characterization (Cexec S1 c1) (Cexec S1 c2) x n).mp hjoin
            exact hm' x n hget.2
          · rename_i v
            have hbeval_s := Beval_sound s1 S1 h2 b v hBeval
            rw [hb_false] at hbeval_s
            cases v with
            | false => simpa [hBeval] using hm'
            | true => exact absurd hbeval_s (by decide : false ≠ true)
  | WHILE b c ih =>
    match h1 with
    | .cexec_while_done hb =>
      let sfix := Cexec S1 (.WHILE b c)
      have hm_sfix : matches' s1 sfix := fixpoint_matches s1 S1 c h2
      constructor
      · simp [cp_com, Cexec]
        apply cexec_mk_WHILE_done s1 (cp_bexp sfix b) (cp_com sfix c)
        rw [cp_bexp_sound s1 sfix hm_sfix b, hb]
      · simp [Cexec]
        exact hm_sfix
    | .cexec_while_loop hb hbody hrec =>
      let sfix := Cexec S1 (.WHILE b c)
      have hm_sfix : matches' s1 sfix := fixpoint_matches s1 S1 c h2
      have hfix : Le (Cexec sfix c) sfix := fixpoint_Le_Cexec S1 c
      have h_body_correct (st st' : store) (hbody' : cexec st c st') (hm : matches' st sfix) :
          (cexec st (cp_com sfix c) st' ∧ matches' st' (Cexec sfix c)) :=
        ih st st' sfix hbody' hm
      rcases h_body_correct s1 _ hbody hm_sfix with ⟨hcex_body, hm_body⟩
      have hm_sfix' : matches' _ sfix :=
        matches_Le _ (Cexec sfix c) sfix hfix hm_body
      have h_while_res :=
        cp_while_correct sfix b c hfix h_body_correct _ s2 hm_sfix' hrec
      rcases h_while_res with ⟨hcex_rec, hm_final⟩
      have hbeval_opt : beval s1 (cp_bexp sfix b) = true := by
        rw [cp_bexp_sound s1 sfix hm_sfix b, hb]
      constructor
      · simp [cp_com, Cexec]
        exact cexec_mk_WHILE_loop (cp_bexp sfix b) (cp_com sfix c) s1 _ s2 hbeval_opt hcex_body hcex_rec
      · simp [Cexec]
        exact hm_final

/-- For all `c`, `s1`, `s2`, `S1`, if `c` executes from `s1` to `s2` and `s1` matches `S1`,
  then `cp_com S1 c` also executes from `s1` to `s2`. -/
theorem cp_com_correct_terminating (c : com) (s1 s2 : store) (S1 : Store) (h1 : cexec s1 c s2) (h2 : matches' s1 S1) :
    cexec s1 (cp_com S1 c) s2 :=
  (cp_com_correct_terminating_aux c s1 s2 S1 h1 h2).1
