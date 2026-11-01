import Frap.SmallStepImp

/-!
# Small-Step Imp Theorems

Theorems about the small-step operational semantics of the IMP imperative language
from Frap's `SmallStepImp` module.  This includes generic lemmas about arithmetic
and boolean expression reduction, assignment increment, conditional reduction, and
key correctness lemmas for the concurrent `par_loop` program.
-/

set_option quotPrecheck false
open Imp
open AExp
open BExp
open Com
open Multi
open AStep
open BStep
open CStep

namespace CImp
open Com

/-! ### Generic reduction lemmas -/

/--
When `st v = k`, the boolean expression `b_eq (a_id v) (a_num k)` reduces to
`b_true` in the `BStep` small-step semantics.  This is a core lemma for reasoning
about concrete conditional guards that compare a state variable to a constant.
-/
theorem beq_id_num_bstep_true (st : State) (v : String) (k : Nat) (h : st v = k) :
    Multi (BStep st) (b_eq (a_id v) (a_num k)) b_true := by
  apply multi_step
  · apply bs_eq1; apply as_id
  · apply multi_step
    · apply bs_eq
    · simpa [h] using multi_refl b_true

/--
Increment assignment: `var := var + 1` in a state where `st var = n` steps to
`(c_skip, var !-> n + 1; st)` in the `CStep` small-step semantics.
-/
theorem asgn_incr_multi (st : State) (var : String) (n : Nat) (h : st var = n) :
    Multi CStep (c_asgn var (a_plus (a_id var) (a_num 1)), st)
      (c_skip, var !-> n + 1; st) := by
  apply multi_step
  · apply CStep.cs_asgnStep; apply as_plus1; apply as_id
  · apply multi_step
    · apply CStep.cs_asgnStep; apply as_plus
    · apply multi_step
      · rw [h]; apply CStep.cs_asgn
      · apply multi_refl

/--
When `st v = k`, the conditional `c_if (b_eq (a_id v) (a_num k)) c₁ c₂` reduces
to `c₁` in the `CStep` small-step semantics.
-/
theorem if_beq_id_num_true_step (st : State) (v : String) (k : Nat) (h : st v = k) (c₁ c₂ : Com) :
    Multi CStep (c_if (b_eq (a_id v) (a_num k)) c₁ c₂, st) (c₁, st) := by
  apply multi_step
  · apply CStep.cs_ifStep; apply bs_eq1; apply as_id
  · apply multi_step
    · apply CStep.cs_ifStep; apply bs_eq
    · apply multi_step
      · simpa [h] using CStep.cs_ifTrue st c₁ c₂
      · apply multi_refl

/-! ### Concurrent `par_loop` correctness lemmas -/

/--
One iteration of the `par_loop` body.  Starting from a state where `x = n` and
`y = 0`, we can reach `(par_loop, x !-> n + 1; st)` — the loop restarts with
`x` incremented and `y` still 0.
-/
theorem par_body_n__Sn n st
    : st x = n ∧ st y = 0
      → Multi CStep (par_loop, st) (par_loop, x !-> n + 1; st) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  apply multi_step
  · apply CStep.cs_par2; apply CStep.cs_while
  · apply multi_step
    · apply CStep.cs_par2; apply CStep.cs_ifStep
      apply bs_eq1; apply as_id
    · apply multi_step
      · apply CStep.cs_par2; apply CStep.cs_ifStep
        apply bs_eq
      · apply multi_step
        · apply CStep.cs_par2
          rw [hy]
          apply CStep.cs_ifTrue
        · apply multi_step
          · apply CStep.cs_par2; apply CStep.cs_seqStep; apply CStep.cs_asgnStep
            apply as_plus1; apply as_id
          · apply multi_step
            · apply CStep.cs_par2; apply CStep.cs_seqStep; apply CStep.cs_asgnStep
              apply as_plus
            · apply multi_step
              · apply CStep.cs_par2; apply CStep.cs_seqStep
                rw [hx]
                apply CStep.cs_asgn
              · apply multi_step
                · apply CStep.cs_par2; apply CStep.cs_seqFinish
                · unfold par_loop
                  apply multi_refl

/--
From a `par_loop` configuration `(par_loop, st')` where `st' x = n'` and
`st' y = 0`, there exists a state `st''` reachable via `par_loop` where
`st'' x = n' + 1` and `st'' y = 0`.  This is the one-step invariance lemma
for `par_loop`.
-/
theorem par_body_n_succ (n' : Nat) (st' : State) (hx' : st' x = n') (hy' : st' y = 0) :
    ∃ st'', Multi CStep (par_loop, st') (par_loop, st'') ∧ st'' x = n' + 1 ∧ st'' y = 0 := by
  have hstep : Multi CStep (par_loop, st') (par_loop, x !-> n' + 1; st') :=
    par_body_n__Sn n' st' ⟨hx', hy'⟩
  refine ⟨x !-> n' + 1; st', hstep, ?_, ?_⟩
  · simp [update]
  · simp [update, hy']
    have hxy : (y : String) ≠ (x : String) := by
      unfold x y
      decide
    exact hxy

/--
**Main correctness theorem for `par_loop`**: Starting from `(par_loop, st)` where
`st x = 0 ∧ st y = 0`, for any natural number `n`, there exists a state `st'`
reachable via `par_loop` where `st' x = n` and `st' y = 0`.  This shows that
`par_loop` can output any natural number in `x`.
-/
theorem par_body_n_1 n st
    : st x = 0 ∧ st y = 0
      → ∃ st', Multi CStep (par_loop, st) (par_loop, st')
          ∧ st' x = n ∧ st' y = 0 := by
  intro h
  obtain ⟨hx, hy⟩ := h
  induction n with
  | zero =>
      exact ⟨st, multi_refl _, hx, hy⟩
  | succ n' hn' =>
      obtain ⟨st', h', hx', hy'⟩ := hn'
      obtain ⟨st'', hstep, hx'', hy''⟩ := par_body_n_succ n' st' hx' hy'
      exact ⟨st'', multi_trans h' hstep, hx'', hy''⟩

end CImp
