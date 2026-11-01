import VerifiedCompiler

open Term (eval)
open Program List
open Instruction hiding exec

namespace Term

/-!
# General lemmas about `exec`
-/

theorem exec_cons_eq_none (hd : Instruction) (tl : Program) (stack : Stack)
    (s : Instruction.Result) (hinst : hd.exec stack = some s)
    (hgoto : goto tl s.offset = none) :
    exec (hd :: tl) stack = none := by
  simp [exec, hinst]
  generalize hres : goto tl s.offset = res
  cases res
  · rfl
  · rename_i val
    rw [hres] at hgoto
    simp at hgoto

theorem exec_cons_eq_some (hd : Instruction) (tl : Program) (stack : Stack)
    (s : Instruction.Result) (p : Program) (hinst : hd.exec stack = some s)
    (hgoto : goto tl s.offset = some p) :
    exec (hd :: tl) stack = exec p s.stack := by
  simp [exec, hinst]
  generalize hres : goto tl s.offset = res
  cases res
  · rw [hres] at hgoto
    simp at hgoto
  · rename_i val
    rw [hres] at hgoto
    injection hgoto with h_eq
    subst h_eq
    rfl

/-!
A key lemma: if a program prefix executes successfully, appending more
instructions runs the suffix from the resulting state.
-/
theorem exec_prog_mono (prog₂ : Program) (h : exec prog₁ s₁ = some s₂) :
    exec (prog₁ ++ prog₂) s₁ = exec prog₂ s₂ := by
  induction prog₁, s₁ using exec.induct with
  | case1 stack =>
    simp [exec] at h
    cases h
    simp
  | case2 hd tl stack hinst =>
    simp [exec, hinst] at h
  | case3 hd tl stack stack_1 offset hinst hgoto =>
    let s : Instruction.Result := { stack := stack_1, offset := offset }
    have hexec : exec (hd :: tl) stack = none :=
      exec_cons_eq_none hd tl stack s hinst hgoto
    rw [hexec] at h
    simp at h
  | case4 hd tl stack stack_1 offset hinst p hgoto hi =>
    let s : Instruction.Result := { stack := stack_1, offset := offset }
    have hexec : exec (hd :: tl) stack = exec p s.stack :=
      exec_cons_eq_some hd tl stack s p hinst hgoto
    rw [hexec] at h
    have h' := hi h
    have hgoto' : goto (tl ++ prog₂) s.offset = some (p ++ prog₂) :=
      goto_mono prog₂ hgoto
    simp [exec, hinst, List.cons_append]
    generalize hres : goto (tl ++ prog₂) s.offset = res
    cases res
    · rw [hres] at hgoto'
      simp at hgoto'
    · rename_i val
      rw [hres] at hgoto'
      injection hgoto' with h_eq
      subst h_eq
      simpa

/-!
# General lemmas about `goto`
-/

theorem goto_cons_one (i : Instruction) (q : Program) : goto (i :: q) 1 = some q := by
  simp [goto]

theorem goto_suffix_plus_one (p : Program) (i : Instruction) (q : Program) :
    goto (p ++ [i] ++ q) (p.length + 1) = some q := by
  induction p with
  | nil => simp [goto_cons_one]
  | cons hd tl ih =>
    simp [goto, List.length_cons, List.cons_append] at *
    exact ih

theorem goto_end' (p : Program) : goto p p.length = some [] := by
  induction p with
  | nil => exact goto.eq_1 []
  | cons hd tl ih =>
    rw [List.length_cons, goto.eq_3]
    exact ih

theorem goto_append_eq (p q : Program) : goto (p ++ q) p.length = some q := by
  induction p with
  | nil => simp [goto]
  | cons i p ih => simpa [goto] using ih

theorem goto_append_offset (p q : Program) (k : Nat) :
    goto (p ++ q) (p.length + k) = goto q k := by
  induction p with
  | nil => simp
  | cons i p ih => simpa [goto, Nat.add_right_comm, Nat.add_assoc] using ih

/-!
# Semantics of individual instructions

The `exec_cons_eq_some` lemma provides the general pattern, but it is
convenient to have specialized lemmas for the common `jez` and `jmp` cases.
-/

theorem exec_jmp_end (p : Program) (s : Stack) :
    exec (Instruction.jmp p.length :: p) s = some s := by
  have h := exec_cons_eq_some (Instruction.jmp p.length) p s
    { stack := s, offset := p.length } []
    (by simp [Instruction.exec]) (goto_end' p)
  simpa [exec] using h

/-- `jez k` on a `0` top-of-stack takes the branch: skip to offset `k` in `prog`. -/
theorem exec_jez_zero (k : Nat) (prog q : Program) (s : Stack)
    (hgoto : goto prog k = some q) :
    exec (Instruction.jez k :: prog) (0 :: s) = exec q s := by
  apply exec_cons_eq_some (Instruction.jez k) prog (0 :: s)
    { stack := s, offset := k } q
    (by simp [Instruction.exec]) hgoto

/-- `jez k` on a nonzero top-of-stack falls through (continues at offset 0). -/
theorem exec_jez_one (k : Nat) (prog : Program) (s : Stack) :
    exec (Instruction.jez k :: prog) (1 :: s) = exec prog s := by
  apply exec_cons_eq_some (Instruction.jez k) prog (1 :: s)
    { stack := s, offset := 0 } prog
    (by simp [Instruction.exec]) (goto.eq_1 prog)

theorem exec_and_cons (a b : Nat) (prog : Program) (s : Stack) :
    exec (Instruction.and :: prog) (b :: a :: s) = exec prog ((a.conj b) :: s) := by
  apply exec_cons_eq_some (Instruction.and) prog (b :: a :: s)
    { stack := a.conj b :: s, offset := 0 } prog
    (by simp [Instruction.exec]) (goto.eq_1 prog)

theorem exec_const_cons (n : Nat) (prog : Program) (s : Stack) :
    exec (Instruction.const n :: prog) s = exec prog (n :: s) := by
  apply exec_cons_eq_some (Instruction.const n) prog s
    { stack := n :: s, offset := 0 } prog
    (by simp [Instruction.exec]) (goto.eq_1 prog)

theorem exec_jmp_skip (p q : Program) (s : Stack) :
    exec (Instruction.jmp p.length :: p ++ q) s = exec q s := by
  exact exec_cons_eq_some (Instruction.jmp p.length) (p ++ q) s
    { stack := s, offset := p.length } q
    (by simp [Instruction.exec]) (goto_append_eq p q)

/-!
# Main theorem: correctness of `lower` for `ite`
-/

theorem lower_ite_hEquiv {cond : Term .bool} {pos neg : Term τ}
    (hc : cond ≈ lower cond) (hp : pos ≈ lower pos) (hn : neg ≈ lower neg) :
    ite cond pos neg ≈ lower (ite cond pos neg) := by
  unfold HEquiv lower
  have h_exec_lower_cond : exec (lower cond) [] = some [cond.eval.toNat] := by
    unfold HEquiv at hc; exact hc
  let p := lower pos
  let n := lower neg
  let rest := [Instruction.jez (p.length + 1)] ++ p ++ [Instruction.jmp n.length] ++ n
  have h_mono : exec (lower cond ++ rest) [] = exec rest [cond.eval.toNat] :=
    exec_prog_mono rest h_exec_lower_cond
  have h_assoc : lower cond ++ [Instruction.jez (p.length + 1)] ++ p ++
    [Instruction.jmp n.length] ++ n = lower cond ++ rest := by
    simp [rest, List.append_assoc]
  rw [h_assoc]
  rw [h_mono]
  clear h_mono h_assoc
  dsimp [rest]
  cases h_ev : cond.eval with
  | bool b =>
    cases b with
    | false =>
      have h_jez := exec_jez_zero (p.length + 1)
        (p ++ [Instruction.jmp n.length] ++ n) n []
        (goto_suffix_plus_one p (Instruction.jmp n.length) n)
      have h_exec_n : exec n [] = some [neg.eval.toNat] := by
        unfold HEquiv at hn; exact hn
      simpa [h_ev, Term.eval, Value.toNat] using (h_jez.trans h_exec_n)
    | true =>
      have h_jez := exec_jez_one (p.length + 1)
        (p ++ [Instruction.jmp n.length] ++ n) []
      have h_exec_p : exec p [] = some [pos.eval.toNat] := by
        unfold HEquiv at hp; exact hp
      have h_prog_mono : exec (p ++ ([Instruction.jmp n.length] ++ n)) [] =
          exec ([Instruction.jmp n.length] ++ n) [pos.eval.toNat] :=
        exec_prog_mono ([Instruction.jmp n.length] ++ n) h_exec_p
      have h_jmp := exec_jmp_end n [pos.eval.toNat]
      have h_full : exec ((Instruction.jez (p.length + 1)) ::
          (p ++ [Instruction.jmp n.length] ++ n)) [1] = some [pos.eval.toNat] := by
        rw [h_jez]
        simpa [List.append_assoc] using (h_prog_mono.trans h_jmp)
      simpa [h_ev, Term.eval, Value.toNat] using h_full

/-!
# Properties of `eval` for `bool` typed terms
-/

theorem eval_toNat_eq_zero_imp_false (t : Term .bool) (h : (eval t).toNat = 0) :
    eval t = Value.bool false := by
  cases he : eval t with
  | bool b => cases b <;> simp_all [Value.toNat]

theorem eval_toNat_ne_zero_imp_true (t : Term .bool) (h : (eval t).toNat ≠ 0) :
    eval t = Value.bool true := by
  cases he : eval t with
  | bool b => cases b <;> simp_all [Value.toNat]

theorem conj_toNat_eq_toNat_and (a b : Term .bool) :
    ((eval a).toNat).conj ((eval b).toNat) = (eval (and a b)).toNat := by
  cases ha : eval a with
  | bool x =>
    cases hb : eval b with
    | bool y => cases x <;> cases y <;> simp [eval, ha, hb, Value.toNat, Nat.conj]

/-!
# Correctness of `lower` for `and` and general lemmas
-/

theorem exec_lower_append (t : Term τ) (prog : Program) (s : Stack) :
    (lower t ++ prog).exec s = prog.exec ((eval t).toNat :: s) := by
  induction t generalizing prog s with
  | val v => simpa [lower] using exec_const_cons v.toNat prog s
  | and lhs rhs ihl ihr =>
    simp only [lower, List.append_assoc]
    rw [ihl, ihr]
    simpa only [List.singleton_append, conj_toNat_eq_toNat_and] using
      exec_and_cons lhs.eval.toNat rhs.eval.toNat prog s
  | ite cond pos neg ihc ihp ihn =>
    simp only [lower, List.append_assoc]
    rw [ihc]
    cases he : cond.eval with
    | bool b =>
      cases b with
      | false =>
        simp only [Value.toNat, List.singleton_append]
        rw [exec_jez_zero ((lower pos).length + 1) _ (lower neg ++ prog) s
          (by simpa [List.append_assoc] using (goto_suffix_plus_one (lower pos) (Instruction.jmp (lower neg).length) (lower neg ++ prog)))]
        simpa [eval, he] using ihn prog s
      | true =>
        simp only [Value.toNat, List.singleton_append]
        rw [exec_jez_one, ihp]
        simpa [eval, he] using exec_jmp_skip (lower neg) prog (pos.eval.toNat :: s)

theorem lower_and_hEquiv (hl : lhs ≈ lower lhs) (hr : rhs ≈ lower rhs) :
    and lhs rhs ≈ lower (and lhs rhs) := by
  simpa [HEquiv, exec] using exec_lower_append (and lhs rhs) [] []

end Term

namespace Program

/-- Executing an empty program leaves the stack unchanged. -/
@[simp]
theorem exec_nil (s : Stack) : exec [] s = some s := by
  simp [exec]

/-- If the current instruction fails (returns `none`), the whole program fails. -/
theorem exec_cons_of_inst_exec_none (hd : Instruction) (tl : Program) (s : Stack)
    (hinst : Instruction.exec hd s = none) : exec (hd :: tl) s = none := by
  simp [exec, hinst]

end Program

namespace Instruction

/-!
# Instruction-level `exec` simplification lemmas

`Instruction.exec` defines the one-step semantics of each VM instruction.
These `@[simp]` lemmas expand each instruction case for common stack shapes,
making proofs about program execution easier.
-/

@[simp]
theorem exec_const (n : Nat) (s : Stack) : exec (.const n) s = some ⟨n :: s, 0⟩ := rfl

@[simp]
theorem exec_and_nil : exec .and ([] : Stack) = none := rfl

@[simp]
theorem exec_and_singleton (a : Nat) : exec .and [a] = none := rfl

@[simp]
theorem exec_and_pair (a b : Nat) (s : Stack) : exec .and (a :: b :: s) = some ⟨(b.conj a) :: s, 0⟩ := rfl

@[simp]
theorem exec_jmp (o : Nat) (s : Stack) : exec (.jmp o) s = some ⟨s, o⟩ := rfl

@[simp]
theorem exec_jez_nil (o : Nat) : exec (.jez o) ([] : Stack) = none := rfl

@[simp]
theorem exec_jez_zero (o : Nat) (s : Stack) : exec (.jez o) (0 :: s) = some ⟨s, o⟩ := rfl

@[simp]
theorem exec_jez_succ (n o : Nat) (s : Stack) : exec (.jez o) ((n + 1) :: s) = some ⟨s, 0⟩ := rfl

/--
If executing a single instruction on stack `s₁` produces ⟨s₂, o⟩, then
appending `s` to the input stack appends `s` to the output stack, keeping
the offset unchanged.
-/
theorem exec_stack_append (s : Stack) (h : exec inst s₁ = some ⟨s₂, o⟩) :
    exec inst (s₁ ++ s) = some ⟨s₂ ++ s, o⟩ := by
  cases inst
  case const n =>
    simp at h ⊢
    rcases h with ⟨hstack, hoffset⟩
    subst hstack hoffset
    simp
  case and =>
    cases s₁
    · simp at h
    · rename_i a as
      cases as
      · simp at h
      · rename_i b bs
        simp at h ⊢
        rcases h with ⟨hstack, hoffset⟩
        subst hstack hoffset
        simp
  case jmp offset =>
    simp at h ⊢
    rcases h with ⟨hstack, hoffset⟩
    subst hstack hoffset
    simp
  case jez offset =>
    cases s₁
    · simp at h
    · rename_i val tl
      cases val
      · simp at h ⊢
        rcases h with ⟨hstack, hoffset⟩
        subst hstack hoffset
        simp
      · rename_i n
        simp at h ⊢
        rcases h with ⟨hstack, hoffset⟩
        subst hstack hoffset
        simp

end Instruction
