import LeroyCompilerVerificationCourse.Compil
import verisoftbench.LeroyCompilerVerificationCourse.DivergenceHelpers

set_option quotPrecheck false

/-!
## Instruction-at lemmas

Lemmas about `instr_at` and its behavior on list concatenation.
-/

/--
If `pc` is within bounds of `C1`, then `instr_at (C1 ++ C2) pc = instr_at C1 pc`.
-/
theorem instr_at_append_left (C1 C2 : List instr) (pc : Int) (hpc_ge : 0 ≤ pc) (hpc_lt : pc < (C1.length : Int)) :
    instr_at (C1 ++ C2) pc = instr_at C1 pc := by
  induction C1 generalizing pc with
  | nil =>
    have : pc < (0 : Int) := by simpa using hpc_lt
    omega
  | cons i C1' ih =>
    rw [List.cons_append]
    simp [instr_at]
    by_cases hzero : pc = 0
    · simp [hzero]
    · simp [hzero]
      apply ih (pc - 1)
      · omega
      · have hlen : (List.length (i :: C1') : Int) = (List.length C1' : Int) + 1 := by simp
        omega

/--
If `k` is within bounds of `C2`, then `instr_at (C1 ++ C2) (C1.length + k) = instr_at C2 k`.
-/
theorem instr_at_append_right (C1 C2 : List instr) (k : Int) (hk_ge : 0 ≤ k) (hk_lt : k < (C2.length : Int)) :
    instr_at (C1 ++ C2) ((C1.length : Int) + k) = instr_at C2 k := by
  induction C1 generalizing k with
  | nil => simp
  | cons i C1' ih =>
    rw [List.cons_append]
    simp [instr_at]
    have hnonzero : (C1'.length : Int) + 1 + k ≠ 0 := by omega
    simp [hnonzero]
    have hsub : ((C1'.length : Int) + 1 + k) - 1 = (C1'.length : Int) + k := by omega
    rw [hsub]
    exact ih k hk_ge hk_lt

/--
If `instr_at C pc` returns `some i`, then `pc` is within the valid range of `C`.
-/
theorem instr_at_some_imp_range (C : List instr) (pc : Int) (i : instr) (h : instr_at C pc = .some i) :
    0 ≤ pc ∧ pc < (C.length : Int) := by
  induction C generalizing pc i with
  | nil => simp [instr_at] at h
  | cons i' C' ih =>
    simp [instr_at] at h
    by_cases hzero : pc = 0
    · subst hzero
      simp at h
      subst h
      simp
    · simp [hzero] at h
      rcases ih (pc - 1) i h with ⟨hge, hlt⟩
      have hge' : 0 ≤ pc := by omega
      have hlt' : pc < ((i' :: C').length : Int) := by
        simp
        omega
      exact ⟨hge', hlt'⟩

/--
If `instr_at C pc` returns `some i`, then so does `instr_at (C ++ D) pc`.
-/
theorem instr_at_some_append_left (C D : List instr) (pc : Int) (i : instr)
    (h : instr_at C pc = .some i) : instr_at (C ++ D) pc = .some i := by
  rcases instr_at_some_imp_range C pc i h with ⟨hge, hlt⟩
  rw [instr_at_append_left C D pc hge hlt]
  exact h

/--
If `instr_at C pc` returns `some i`, then `instr_at (C_pre ++ C) (C_pre.length + pc)` also returns `some i`.
-/
theorem instr_at_some_append_right (C_pre C : List instr) (pc : Int) (i : instr)
    (h : instr_at C pc = .some i) :
    instr_at (C_pre ++ C) ((C_pre.length : Int) + pc) = .some i := by
  rcases instr_at_some_imp_range C pc i h with ⟨hge, hlt⟩
  rw [instr_at_append_right C_pre C pc hge hlt]
  exact h

/--
`instr_at` at the end of the list (after the last element) returns `some` of the appended instruction.
-/
theorem instr_at_snoc (C : List instr) (i : instr) :
    instr_at (C ++ [i]) (C.length : Int) = .some i := by
  simpa using instr_at_append_right C [i] (0 : Int) (by omega) (by simp)

/--
`instr_at (C1 ++ i :: C3) (codelen C1) = .some i`:
the instruction at position `codelen C1` in a list `C1 ++ (i :: C3)` is `i`.
This is more general than `instr_at_snoc` since it allows trailing instructions `C3`.
-/
theorem instr_at_codelen_cons (C1 : List instr) (i : instr) (C3 : List instr) :
    instr_at (C1 ++ (i :: C3)) (codelen C1) = .some i := by
  have h := instr_at_append_right C1 (i :: C3) (0 : Int) (by omega) (by simp)
  simpa [codelen, Int.add_zero] using h

/-!
## Transition lifting and shifting lemmas

Lemmas about lifting and shifting `transition` and `star (transition)` along list concatenation.
-/

/--
Lifting a transition on `C` to `C ++ D`: if `transition C a b`, then `transition (C ++ D) a b`.
-/
theorem transition_lift_right (C D : List instr) (a b : config)
    (h : transition C a b) :
    transition (C ++ D) a b := by
  match h with
  | .trans_const pc stk s n h_at =>
    simpa using transition.trans_const (C := C ++ D) (pc := pc) (stk := stk) (s := s) (n := n)
      (instr_at_some_append_left C D pc (.Iconst n) h_at)
  | .trans_var pc stk s x h_at =>
    simpa using transition.trans_var (C := C ++ D) (pc := pc) (stk := stk) (s := s) (x := x)
      (instr_at_some_append_left C D pc (.Ivar x) h_at)
  | .trans_setvar pc stk s x n h_at =>
    simpa using transition.trans_setvar (C := C ++ D) (pc := pc) (stk := stk) (s := s) (x := x) (n := n)
      (instr_at_some_append_left C D pc (.Isetvar x) h_at)
  | .trans_add pc stk s n1 n2 h_at =>
    simpa using transition.trans_add (C := C ++ D) (pc := pc) (stk := stk) (s := s) (n1 := n1) (n2 := n2)
      (instr_at_some_append_left C D pc .Iadd h_at)
  | .trans_opp pc stk s n h_at =>
    simpa using transition.trans_opp (C := C ++ D) (pc := pc) (stk := stk) (s := s) (n := n)
      (instr_at_some_append_left C D pc .Iopp h_at)
  | .trans_branch pc stk s d pc' h_at h_eq =>
    simpa using transition.trans_branch (C := C ++ D) (pc := pc) (stk := stk) (s := s) (d := d) (pc' := pc')
      (instr_at_some_append_left C D pc (.Ibranch d) h_at) h_eq
  | .trans_beq pc stk s d1 d0 n1 n2 pc' h_at h_eq =>
    simpa using transition.trans_beq (C := C ++ D) (pc := pc) (stk := stk) (s := s) (d1 := d1) (d0 := d0)
      (n1 := n1) (n2 := n2) (pc' := pc')
      (instr_at_some_append_left C D pc (.Ibeq d1 d0) h_at) h_eq
  | .trans_ble pc stk s d1 d0 n1 n2 pc' h_at h_eq =>
    simpa using transition.trans_ble (C := C ++ D) (pc := pc) (stk := stk) (s := s) (d1 := d1) (d0 := d0)
      (n1 := n1) (n2 := n2) (pc' := pc')
      (instr_at_some_append_left C D pc (.Ible d1 d0) h_at) h_eq

/--
Lifting a `star (transition C)` to `star (transition (C ++ D))`.
If `star (transition C) a b`, then also `star (transition (C ++ D)) a b`.
-/
theorem star_lift_right (C D : List instr) (a b : config)
    (h : star (transition C) a b) :
    star (transition (C ++ D)) a b := by
  induction h with
  | star_refl _ => exact star.star_refl _
  | star_step h_step h_star ih =>
    exact star.star_step (transition_lift_right C D _ _ h_step) ih

/--
Shifting a transition on `C` by prepending `C_pre`: the program counter is offset by `C_pre.length`.
-/
theorem transition_shift_right (C_pre C : List instr) (pc pc' : Int) (stk stk' : stack) (s s' : store)
    (h : transition C (pc, stk, s) (pc', stk', s')) :
    transition (C_pre ++ C) ((C_pre.length : Int) + pc, stk, s) ((C_pre.length : Int) + pc', stk', s') := by
  match h with
  | .trans_const pc_v stk_v s_v n h_at =>
    simpa [Int.add_assoc] using
      transition.trans_const (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (n := n)
        (instr_at_some_append_right C_pre C pc_v (.Iconst n) h_at)
  | .trans_var pc_v stk_v s_v x h_at =>
    simpa [Int.add_assoc] using
      transition.trans_var (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (x := x)
        (instr_at_some_append_right C_pre C pc_v (.Ivar x) h_at)
  | .trans_setvar pc_v stk_v s_v x n h_at =>
    simpa [Int.add_assoc] using
      transition.trans_setvar (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (x := x) (n := n)
        (instr_at_some_append_right C_pre C pc_v (.Isetvar x) h_at)
  | .trans_add pc_v stk_v s_v n1 n2 h_at =>
    simpa [Int.add_assoc] using
      transition.trans_add (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (n1 := n1) (n2 := n2)
        (instr_at_some_append_right C_pre C pc_v .Iadd h_at)
  | .trans_opp pc_v stk_v s_v n h_at =>
    simpa [Int.add_assoc] using
      transition.trans_opp (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (n := n)
        (instr_at_some_append_right C_pre C pc_v .Iopp h_at)
  | .trans_branch pc_v stk_v s_v d pc''_v h_at h_eq =>
    simpa [Int.add_assoc] using
      transition.trans_branch (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (d := d)
        (pc' := (C_pre.length : Int) + pc''_v)
        (instr_at_some_append_right C_pre C pc_v (.Ibranch d) h_at) (by omega)
  | .trans_beq pc_v stk_v s_v d1 d0 n1 n2 pc''_v h_at h_eq =>
    simpa [Int.add_assoc] using
      transition.trans_beq (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (d1 := d1) (d0 := d0) (n1 := n1) (n2 := n2)
        (pc' := (C_pre.length : Int) + pc''_v)
        (instr_at_some_append_right C_pre C pc_v (.Ibeq d1 d0) h_at) (by omega)
  | .trans_ble pc_v stk_v s_v d1 d0 n1 n2 pc''_v h_at h_eq =>
    simpa [Int.add_assoc] using
      transition.trans_ble (C := C_pre ++ C) (pc := (C_pre.length : Int) + pc_v)
        (stk := stk_v) (s := s_v) (d1 := d1) (d0 := d0) (n1 := n1) (n2 := n2)
        (pc' := (C_pre.length : Int) + pc''_v)
        (instr_at_some_append_right C_pre C pc_v (.Ible d1 d0) h_at) (by omega)

/--
Shifting a `star (transition C)` by prepending `C_pre`: the program counter is offset by `C_pre.length`.
-/
theorem star_shift_right (C_pre C : List instr) (a b : config)
    (h : star (transition C) a b) :
    star (transition (C_pre ++ C)) ((C_pre.length : Int) + a.1, a.2.1, a.2.2)
      ((C_pre.length : Int) + b.1, b.2.1, b.2.2) := by
  induction h with
  | star_refl _ => exact star.star_refl _
  | @star_step x y z h_step h_star ih =>
    have h_lift : transition (C_pre ++ C) ((C_pre.length : Int) + x.1, x.2.1, x.2.2)
        ((C_pre.length : Int) + y.1, y.2.1, y.2.2) :=
      transition_shift_right C_pre C x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2 h_step
    exact star.star_step h_lift ih

/-!
## Compilation correctness
-/

/--
Correctness of arithmetic expression compilation: executing the compiled code
for `a` leaves the stack with `aeval s a` on top, and advances to the end of the code.
-/
theorem compile_aexp_correct_1 (s : store) (a : aexp) (stk : stack) :
  transitions (compile_aexp a) (0, stk, s) (codelen (compile_aexp a), aeval s a :: stk, s) := by
  have steps_trans {α : Type} {R : α → α → Prop} {a b c : α}
      (h : star R a b) (k : star R b c) : star R a c := by
    induction h with
    | star_refl => exact k
    | star_step h _ ih => exact .star_step h (ih k)
  have append_execution (C D : List instr) (s : store)
      (stk mid out : stack) (pc : Int)
      (h : transitions C (0, stk, s) (codelen C, mid, s))
      (k : transitions D (0, mid, s) (pc, out, s)) :
      transitions (C ++ D) (0, stk, s) (codelen C + pc, out, s) := by
    apply steps_trans (star_lift_right C D _ _ h)
    simpa [codelen] using star_shift_right C D _ _ k
  induction a generalizing stk with
  | CONST n =>
    exact .star_step (.trans_const 0 stk s n (by simp [compile_aexp, instr_at]))
      (.star_refl _)
  | VAR x =>
    exact .star_step (.trans_var 0 stk s x (by simp [compile_aexp, instr_at]))
      (.star_refl _)
  | PLUS a b ia ib =>
    have hab := append_execution (compile_aexp a) (compile_aexp b) s stk
      (aeval s a :: stk) (aeval s b :: aeval s a :: stk) _ (ia stk) (ib _)
    have hs : transitions [instr.Iadd] (0, aeval s b :: aeval s a :: stk, s)
        (1, (aeval s a + aeval s b) :: stk, s) :=
      .star_step (.trans_add 0 stk s _ _ (by simp [instr_at])) (.star_refl _)
    have h := append_execution (compile_aexp a ++ compile_aexp b) [instr.Iadd] s
      stk _ _ 1 (by simpa [codelen] using hab) hs
    simpa [compile_aexp, aeval, codelen] using h
  | MINUS a b ia ib =>
    have hab := append_execution (compile_aexp a) (compile_aexp b) s stk
      (aeval s a :: stk) (aeval s b :: aeval s a :: stk) _ (ia stk) (ib _)
    have hs : transitions [instr.Iopp, instr.Iadd]
        (0, aeval s b :: aeval s a :: stk, s)
        (2, (aeval s a + -aeval s b) :: stk, s) :=
      .star_step (.trans_opp 0 (aeval s a :: stk) s _ (by simp [instr_at]))
        (.star_step (.trans_add 1 stk s _ _ (by simp [instr_at])) (.star_refl _))
    have h := append_execution (compile_aexp a ++ compile_aexp b) [instr.Iopp, instr.Iadd]
      s stk _ _ 2 (by simpa [codelen] using hab) hs
    simpa [compile_aexp, aeval, codelen, Int.sub_eq_add_neg] using h

/--
Correctness of boolean expression compilation: executing the compiled code
for `b` with branch targets `d1` (true) and `d0` (false) leaves the stack
and store unchanged, and advances the program counter to the end of the
compiled code plus the appropriate branch offset determined by `beval s b`.
-/
theorem compile_bexp_correct (s : store) (b : bexp) (d1 d0 : Int) (stk : stack) :
    transitions (compile_bexp b d1 d0)
        (0, stk, s)
        (codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s) := by
  have steps_trans {α : Type} {R : α → α → Prop} {a b c : α}
      (h : star R a b) (k : star R b c) : star R a c := by
    induction h with
    | star_refl => exact k
    | star_step h _ ih => exact .star_step h (ih k)
  have append_execution (C D : List instr) (s : store)
      (stk mid out : stack) (pc : Int)
      (h : transitions C (0, stk, s) (codelen C, mid, s))
      (k : transitions D (0, mid, s) (pc, out, s)) :
      transitions (C ++ D) (0, stk, s) (codelen C + pc, out, s) := by
    apply steps_trans (star_lift_right C D _ _ h)
    simpa [codelen] using star_shift_right C D _ _ k
  induction b generalizing d1 d0 with
  | TRUE =>
    by_cases hd : d1 = 0
    · simpa [compile_bexp, beval, hd, codelen] using
        (star.star_refl (R := transition []) (0, stk, s))
    · simpa [compile_bexp, beval, hd, codelen] using
        (star.star_step (transition.trans_branch (C := [instr.Ibranch d1])
          0 stk s d1 (1 + d1) (by simp [instr_at]) (by omega)) (.star_refl _))
  | FALSE =>
    by_cases hd : d0 = 0
    · simpa [compile_bexp, beval, hd, codelen] using
        (star.star_refl (R := transition []) (0, stk, s))
    · simpa [compile_bexp, beval, hd, codelen] using
        (star.star_step (transition.trans_branch (C := [instr.Ibranch d0])
          0 stk s d0 (1 + d0) (by simp [instr_at]) (by omega)) (.star_refl _))
  | EQUAL a b =>
    have hab := append_execution (compile_aexp a) (compile_aexp b) s stk
      (aeval s a :: stk) (aeval s b :: aeval s a :: stk) _
      (compile_aexp_correct_1 s a stk) (compile_aexp_correct_1 s b _)
    have hs := star.star_step (transition.trans_beq (C := [instr.Ibeq d1 d0])
      0 stk s d1 d0 (aeval s a) (aeval s b)
      (1 + if aeval s a = aeval s b then d1 else d0)
      (by simp [instr_at]) (by omega)) (.star_refl _)
    have h := append_execution (compile_aexp a ++ compile_aexp b) [instr.Ibeq d1 d0]
      s stk _ _ _ (by simpa [codelen] using hab) hs
    simpa [compile_bexp, beval, codelen, Int.add_assoc] using h
  | LESSEQUAL a b =>
    have hab := append_execution (compile_aexp a) (compile_aexp b) s stk
      (aeval s a :: stk) (aeval s b :: aeval s a :: stk) _
      (compile_aexp_correct_1 s a stk) (compile_aexp_correct_1 s b _)
    have hs := star.star_step (transition.trans_ble (C := [instr.Ible d1 d0])
      0 stk s d1 d0 (aeval s a) (aeval s b)
      (1 + if aeval s a ≤ aeval s b then d1 else d0)
      (by simp [instr_at]) (by omega)) (.star_refl _)
    have h := append_execution (compile_aexp a ++ compile_aexp b) [instr.Ible d1 d0]
      s stk _ _ _ (by simpa [codelen] using hab) hs
    simpa [compile_bexp, beval, codelen, Int.add_assoc] using h
  | NOT b ih =>
    cases he : beval s b <;> simpa [compile_bexp, beval, he] using ih d0 d1
  | AND a b ia ib =>
    let ca := compile_bexp a 0 (codelen (compile_bexp b d1 d0) + d0)
    let cb := compile_bexp b d1 d0
    have ha := ia 0 (codelen cb + d0)
    cases he : beval s a with
    | false =>
      have h := star_lift_right ca cb _ _ ha
      simpa [ca, cb, compile_bexp, beval, he, codelen, Int.add_assoc] using h
    | true =>
      have h := append_execution ca cb s stk stk stk _
        (by simpa [ca, he] using ha) (ib d1 d0)
      simpa [ca, cb, compile_bexp, beval, he, codelen, Int.add_assoc] using h

/-!
## Compiler correctness for diverging programs
-/

/--
Compiler correctness for diverging programs: if the source program `c`
diverges under the continuation-based small-step semantics (i.e., there
is an infinite sequence of `step` transitions from `(c, .Kstop, s)`),
then the compiled machine code also diverges (i.e., there is an infinite
sequence of `transition` steps from the initial machine state).

This is the complement of `StackMachine.compile_com_correct_terminating`
(from the repo), which handles the terminating case.
-/
theorem compile_program_correct_diverging (c : com) (s : store)
    (h : infseq step (c, .Kstop, s)) : machine_diverges (compile_program c) s := by
  exact LibraryCompilerCorrectness.compile_program_correct_diverging c s h
