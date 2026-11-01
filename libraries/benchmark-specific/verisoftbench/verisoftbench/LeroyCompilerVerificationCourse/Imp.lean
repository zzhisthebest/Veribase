import LeroyCompilerVerificationCourse.Imp
import verisoftbench.LeroyCompilerVerificationCourse.Sequences

set_option quotPrecheck false

/-!
## Big-step to small-step semantics equivalence for IMP

Theorems relating `cexec` (big-step operational semantics) to `red` (small-step
reduction semantics) for IMP commands, complementing the existing `reds_to_cexec`
theorem in the repo.
-/

/--
If `star red (c, s) (.SKIP, s')`, then prepending the sequence `c'` to `c`
preserves the transition: `star red ((c ;; c'), s) (c', s')`.
-/
theorem red_seq_star (c c' : com) (s s' : store)
    (h : star red (c, s) (.SKIP, s')) : star red ((c ;; c'), s) (c', s') := by
  refine star_trans (red_seq_steps c' c .SKIP s s' h)
    (lcc_star_one red (red.red_seq_done c' s'))

/--
Big-step to small-step: if `cexec s c s'` (big-step), then there exists a
finite sequence of reductions `star red (c, s) (.SKIP, s')` (small-step).
This is the converse of `reds_to_cexec` in the repo.
-/
theorem cexec_to_reds (s s' : store) (c : com) : cexec s c s' → star red (c, s) (.SKIP, s') := by
  intro h
  induction h
  case cexec_skip s =>
      exact star.star_refl _
  case cexec_assign s x a =>
      exact lcc_star_one red (red.red_assign x a s)
  case cexec_seq s c1 smid c2 sfinal h1 h2 ih1 ih2 =>
      exact star_trans (red_seq_star c1 c2 s smid ih1) ih2
  case cexec_ifthenelse s b c1 c2 sfinal h' ih =>
      apply star.star_step (red.red_ifthenelse b c1 c2 s)
      exact ih
  case cexec_while_done s b c hb =>
      exact lcc_star_one red (red.red_while_done b c s hb)
  case cexec_while_loop s b c smid sfinal hb h1 h2 ih1 ih2 =>
      apply star.star_step (red.red_while_loop b c s hb)
      exact star_trans (red_seq_star c (.WHILE b c) s smid ih1) ih2

/-!
## Bridge lemmas: step semantics ↔ red semantics

These lemmas relate the continuation-based step semantics (`step`) to the
reduction semantics (`red`) via the `apply_cont` function.
-/

/--
If `red (c, s) (c', s')`, then extending both sides with continuation `k`
preserves the reduction: `red (apply_cont k c, s) (apply_cont k c', s')`.
-/
theorem apply_cont_red (k : cont) (c c' : com) (s s' : store) (h : red (c, s) (c', s')) :
    red (apply_cont k c, s) (apply_cont k c', s') := by
  induction k generalizing c c' s s' with
  | Kstop => simpa [apply_cont]
  | Kseq c1 k1 ih =>
    simp [apply_cont]
    apply ih
    exact red.red_seq_step c c1 s c' s' h
  | Kwhile b c1 k1 ih =>
    simp [apply_cont]
    apply ih
    exact red.red_seq_step c (.WHILE b c1) s c' s' h

/--
A single `step` transition can be simulated by zero or more `red` transitions
after applying the continuation to both source and target.
-/
theorem step_to_star_red (x y : com × cont × store) (h : step x y) :
    star red (apply_cont x.2.1 x.1, x.2.2) (apply_cont y.2.1 y.1, y.2.2) := by
  cases h with
  | step_assign x a k s =>
    have hred : red (.ASSIGN x a, s) (.SKIP, update x (aeval s a) s) :=
      red.red_assign x a s
    have h' := apply_cont_red k (.ASSIGN x a) (.SKIP) s (update x (aeval s a) s) hred
    exact lcc_star_one red h'
  | step_seq c1 c2 s k =>
    simp [apply_cont]
    exact star.star_refl _
  | step_ifthenelse b c1 c2 k s =>
    have hred : red (.IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s) :=
      red.red_ifthenelse b c1 c2 s
    have h' := apply_cont_red k (.IFTHENELSE b c1 c2)
      (if beval s b then c1 else c2) s s hred
    exact lcc_star_one red h'
  | step_while_done b c k s hbeval =>
    have hred : red (.WHILE b c, s) (.SKIP, s) :=
      red.red_while_done b c s hbeval
    have h' := apply_cont_red k (.WHILE b c) (.SKIP) s s hred
    exact lcc_star_one red h'
  | step_while_true b c k s hbeval =>
    have hred : red (.WHILE b c, s) (.SEQ c (.WHILE b c), s) :=
      red.red_while_loop b c s hbeval
    have h' := apply_cont_red k (.WHILE b c) (.SEQ c (.WHILE b c)) s s hred
    simpa [apply_cont] using lcc_star_one red h'
  | step_skip_seq c k s =>
    have hred : red (.SEQ .SKIP c, s) (c, s) :=
      red.red_seq_done c s
    have h' := apply_cont_red k (.SEQ .SKIP c) c s s hred
    simpa [apply_cont] using lcc_star_one red h'
  | step_skip_while b c k s =>
    have hred : red (.SEQ .SKIP (.WHILE b c), s) (.WHILE b c, s) :=
      red.red_seq_done (.WHILE b c) s
    have h' := apply_cont_red k (.SEQ .SKIP (.WHILE b c)) (.WHILE b c) s s hred
    simpa [apply_cont] using lcc_star_one red h'

/--
Lifting `step_to_star_red` to the reflexive-transitive closure:
`star step` implies `star red` after applying the continuation.
-/
theorem star_step_to_star_red (x y : com × cont × store) (h : star step x y) :
    star red (apply_cont x.2.1 x.1, x.2.2) (apply_cont y.2.1 y.1, y.2.2) := by
  induction h with
  | star_refl x => exact star.star_refl _
  | @star_step x w y hstep hstar ih =>
    have h_one : star red (apply_cont x.2.1 x.1, x.2.2) (apply_cont w.2.1 w.1, w.2.2) :=
      step_to_star_red x w hstep
    exact star_trans h_one ih

/--
If the step semantics (with empty continuation) reduces `c` to `SKIP`,
then the big-step semantics also terminates: `cexec s c s'`.

This bridges the continuation-based small-step semantics to the
big-step semantics, via the reduction semantics.
-/
theorem star_step_Kstop_to_cexec (c : com) (s s' : store)
    (h : star step (c, .Kstop, s) (.SKIP, .Kstop, s')) : cexec s c s' := by
  have h_red : star red (apply_cont .Kstop c, s) (apply_cont .Kstop .SKIP, s') :=
    star_step_to_star_red (c, .Kstop, s) (.SKIP, .Kstop, s') h
  simp [apply_cont] at h_red
  exact reds_to_cexec s s' c h_red
