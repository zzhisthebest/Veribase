import Juvix.Core.Main.Semantics.Approx.Indexed
import Juvix.Core.Main.Semantics.Approx
import verisoftbench.Common.Nat.Basic
import verisoftbench.Common.List.Basic

open Juvix.Core.Main

namespace Juvix.Core.Main

/-! Lemmas about indexed approximation relations harvested from solved training problems. -/

/-! ### Indexed-to-non-indexed evaluation -/

/--
If `Eval.Indexed n env e v` holds, then `Eval env e v` also holds.
The indexed evaluation relation witnesses the same reduction but tracks an
approximation depth bound `n`.
-/
lemma Eval.Indexed.toEval {env e v n} (h : Eval.Indexed n env e v) : Eval env e v := by
  induction h with
  | var h => exact .var h
  | var_rec h _ ih => exact .var_rec h ih
  | unit => exact .unit
  | const => exact .const
  | constr => exact .constr
  | app _ _ _ _ ihf iha ihb => exact .app ihf iha ihb
  | constr_app _ _ _ ihc iha => exact .constr_app ihc iha
  | binop _ _ iha ihb => exact .binop iha ihb
  | lambda => exact .lambda
  | save _ _ _ ihv ihb => exact .save ihv ihb
  | branch_matches _ _ ihb => exact .branch_matches ihb
  | branch_fails hn _ ihb => exact .branch_fails hn ihb
  | recur _ _ ihb => exact .recur ihb

/-! ### Non-indexed approximation lemmas -/

/--
Given `closure_inv_right h` where the right-hand side is already known to be a
`Value.closure`, eliminate the existential to obtain the body relation directly.
This is the curried form: takes `a₁`, `a₂`, and the approximation proof `ha` as
explicit arguments, convenient for `apply`/`exact` usage.
-/
lemma Value.Approx.closure_inv_right_curried {env₁ body₁ env₂ body₂}
    (h : Value.closure env₁ body₁ ≲ᵥ Value.closure env₂ body₂) {a₁ a₂}
    (ha : a₁ ≲ᵥ a₂) : body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂ := by
  have h_inv := Value.Approx.closure_inv_right h
  rcases h_inv with ⟨env₂', body₂', h_eq, h_res⟩
  cases h_eq
  exact h_res a₁ a₂ ha

/--
Given `closure_inv_right h` for a general right-hand side `v`, apply the
argument approximation to eliminate the `∀` quantifier while preserving the
existential wrapper. Useful when `v` is not yet known to be a `Value.closure`.
-/
lemma Value.Approx.closure_inv_right_with_arg {env₁ body₁ v a₁ a₂}
    (h : Value.closure env₁ body₁ ≲ᵥ v) (ha : a₁ ≲ᵥ a₂) :
    ∃ env₂ body₂, v = Value.closure env₂ body₂ ∧
      body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂ := by
  have h_inv := Value.Approx.closure_inv_right h
  rcases h_inv with ⟨env₂, body₂, h_eq, h_res⟩
  exact ⟨env₂, body₂, h_eq, h_res a₁ a₂ ha⟩

/--
If two closures are related by approximation, then applying approximating
arguments to their bodies preserves the approximation relation. This is the
`∀` form, useful for `intro`-based proofs.
-/
lemma Value.Approx.closure_inv_1 {env₁ body₁ env₂ body₂}
    (h : Value.closure env₁ body₁ ≲ᵥ Value.closure env₂ body₂) :
    ∀ a₁ a₂, a₁ ≲ᵥ a₂ → body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂ := by
  intro a₁ a₂ ha
  exact Value.Approx.closure_inv_right_curried h ha

lemma Value.Approx.Indexed.weaken {m n v₁ v₂} (h : v₁ ≲ᵥ(m + n) v₂) : v₁ ≲ᵥ(m) v₂ := by
  have hinv := Value.Approx.Indexed.invert h
  cases hinv with
  | unit => exact Value.Approx.Indexed.unit
  | const => exact Value.Approx.Indexed.const
  | constr_app hargs =>
    apply Value.Approx.Indexed.constr_app
    intro k hk
    apply hargs k
    exact Nat.lt_of_lt_of_le hk (Nat.le_add_right m n)
  | closure hbody =>
    apply Value.Approx.Indexed.closure
    intro n₁ n₂ hn
    apply hbody n₁ n₂
    exact Nat.lt_of_lt_of_le hn (Nat.le_add_right m n)

lemma Value.Approx.Indexed.monotone {n₁ n₂ v₁ v₂} (h : v₁ ≲ᵥ(n₁) v₂) (hle : n₂ ≤ n₁) :
    v₁ ≲ᵥ(n₂) v₂ := by
  rcases Nat.le.dest hle with ⟨k, hk⟩
  rw [← hk] at h
  exact Value.Approx.Indexed.weaken h

/--
If all values are self-approximating at depth `n`, then they are also
self-approximating at any smaller depth `m`.
-/
lemma Value.Approx.Indexed.refl_weaken {n m}
    (hrefl : ∀ v, v ≲ᵥ(n) v) (hm : m ≤ n) : ∀ v, v ≲ᵥ(m) v := by
  intro v
  exact Value.Approx.Indexed.monotone (hrefl v) hm

/--
Given indexed evaluation and value reflexivity at a larger depth,
the result value approximates itself in the non-indexed evaluation.
-/
lemma Eval.Indexed.toEval_with_refl {n n₁ n₂ env e v₁}
    (hrefl : ∀ v, v ≲ᵥ(n) v) (heval_idx : Eval.Indexed n₁ env e v₁) (hadd : n₁ + n₂ ≤ n) :
    ∃ v', Eval env e v' ∧ v₁ ≲ᵥ(n₂) v' := by
  have hn₂ : n₂ ≤ n := Nat.le_of_add_le_right n₁ n₂ n hadd
  refine ⟨v₁, Eval.Indexed.toEval heval_idx, ?_⟩
  exact Value.Approx.Indexed.refl_weaken hrefl hn₂ v₁

lemma Env.Approx.Indexed'.monotone {n₁ n₂ env₁ env₂} (h : env₁ ≲ₑ'(n₁) env₂) (hle : n₂ ≤ n₁) :
    env₁ ≲ₑ'(n₂) env₂ := by
  let rec object_depth_mono {n₁ n₂ : Nat} {o₁ o₂ : Object}
      (h : o₁ ≲ₒ'(n₁) o₂) (hle : n₂ ≤ n₁) : o₁ ≲ₒ'(n₂) o₂ := by
    cases h with
    | value hv => exact .value (Value.Approx.Indexed.monotone hv hle)
    | delayed he =>
      apply Object.Approx.Indexed'.delayed
      intro k l v hkl hv
      exact he k l v (Nat.le_trans hkl hle) hv
    | delayed_eq he => exact .delayed_eq (env_depth_mono he hle),
  env_depth_mono {n₁ n₂ : Nat} {env₁ env₂ : Env}
      (h : env₁ ≲ₑ'(n₁) env₂) (hle : n₂ ≤ n₁) : env₁ ≲ₑ'(n₂) env₂ := by
    cases h with
    | nil => exact .nil
    | cons ho ht => exact .cons (object_depth_mono ho hle) (env_depth_mono ht hle)
  exact env_depth_mono h hle

lemma Object.Approx.Indexed'.monotone {n₁ n₂ o₁ o₂} (h : o₁ ≲ₒ'(n₁) o₂) (hle : n₂ ≤ n₁) :
    o₁ ≲ₒ'(n₂) o₂ := by
  let rec object_depth_mono {n₁ n₂ : Nat} {o₁ o₂ : Object}
      (h : o₁ ≲ₒ'(n₁) o₂) (hle : n₂ ≤ n₁) : o₁ ≲ₒ'(n₂) o₂ := by
    cases h with
    | value hv => exact .value (Value.Approx.Indexed.monotone hv hle)
    | delayed he =>
      apply Object.Approx.Indexed'.delayed
      intro k l v hkl hv
      exact he k l v (Nat.le_trans hkl hle) hv
    | delayed_eq he => exact .delayed_eq (env_depth_mono he hle),
  env_depth_mono {n₁ n₂ : Nat} {env₁ env₂ : Env}
      (h : env₁ ≲ₑ'(n₁) env₂) (hle : n₂ ≤ n₁) : env₁ ≲ₑ'(n₂) env₂ := by
    cases h with
    | nil => exact .nil
    | cons ho ht => exact .cons (object_depth_mono ho hle) (env_depth_mono ht hle)
  exact object_depth_mono h hle

lemma forall₂_map_value {n} {vs₁ vs₂ : List Value}
    (h : List.Forall₂ (Value.Approx.Indexed n) vs₁ vs₂) :
    List.Forall₂ (Object.Approx.Indexed' n) (vs₁.map Object.value) (vs₂.map Object.value) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hv htail ih =>
    exact List.Forall₂.cons (Object.Approx.Indexed'.value hv) ih

lemma env_ext_approx {n} {env₁ env₂ : Env} {v₁ v₂ : Value}
    (henv : env₁ ≲ₑ'(n) env₂) (hv : v₁ ≲ᵥ(n) v₂) :
    (Object.value v₁ :: env₁) ≲ₑ'(n) (Object.value v₂ :: env₂) := by
  apply List.Forall₂.cons (Object.Approx.Indexed'.value hv)
  exact henv

lemma construct_env_approx {n env₁ env₂ v₁ v₂}
    (henv : env₁ ≲ₑ'(n) env₂) (hv : v₁ ≲ᵥ(n) v₂) :
    (v₁ ∷ env₁) ≲ₑ'(n) (v₂ ∷ env₂) :=
  env_ext_approx henv hv

/--
If all values are self-approximating at depth `n`, then every object is also
self-approximating at depth `n`.
-/
lemma Object.Approx.Indexed'.refl_of_value_refl {n o} (h : ∀ v, v ≲ᵥ(n) v) : o ≲ₒ'(n) o := by
  cases o with
  | value v => exact Object.Approx.Indexed'.value (h v)
  | delayed env e =>
    apply Object.Approx.Indexed'.delayed
    intro n₁ n₂ v₁ hn₁₂ heval_idx
    exact Eval.Indexed.toEval_with_refl h heval_idx hn₁₂

lemma Value.Approx.Indexed.preserved_step_1 {k} :
    (∀ k' < k, Preservation k') → Preservation k := by
  have delayed_inv {n : Nat} {env : Env} {e : Expr} {b : Object}
      (h : Object.delayed env e ≲ₒ'(n) b) :
      (∃ env' e', e ≲(n)⟨env, env'⟩ e' ∧ b = Object.delayed env' e') ∨
      (∃ env', env ≲ₑ'(n) env' ∧ b = Object.delayed env' e) := by
    cases h with
    | delayed h => exact Or.inl ⟨_, _, h, rfl⟩
    | delayed_eq h => exact Or.inr ⟨_, h, rfl⟩
  have delayed_lookup {n i : Nat} {env₁ env₂ env : Env} {e : Expr}
      (h₁ : env₁ ≲ₑ'(n) env₂)
      (h₂ : env₁[i]? = some (Object.delayed env e)) :
      (∃ env' e', e ≲(n)⟨env, env'⟩ e' ∧ env₂[i]? = some (Object.delayed env' e')) ∨
      (∃ env', env ≲ₑ'(n) env' ∧ env₂[i]? = some (Object.delayed env' e)) := by
    induction h₁ generalizing i with
    | nil => simp at h₂
    | @cons a b as bs hhead htail ih =>
      cases i with
      | zero =>
        have ha : a = Object.delayed env e := by simpa using h₂
        subst a
        rcases delayed_inv hhead with
          (⟨env', e', h, rfl⟩ | ⟨env', h, rfl⟩)
        · exact Or.inl ⟨env', e', h, by simp⟩
        · exact Or.inr ⟨env', h, by simp⟩
      | succ i =>
        rcases ih (by simpa using h₂) with
          (⟨env', e', h, hg⟩ | ⟨env', h, hg⟩)
        · exact Or.inl ⟨env', e', h, by simpa using hg⟩
        · exact Or.inr ⟨env', h, by simpa using hg⟩
  have value_lookup {n i : ℕ} {env₁ env₂ : Env} {v : Value}
      (h : env₁ ≲ₑ'(n) env₂) (hg : env₁[i]? = some (Object.value v)) :
      ∃ v', env₂[i]? = some (Object.value v') ∧ v ≲ᵥ(n) v' := by
    induction h generalizing i with
    | nil => simp at hg
    | @cons a b as bs hab ht ih =>
      cases i with
      | zero =>
        have ha : a = Object.value v := by simpa using hg
        subst a
        cases hab with
        | value hv => exact ⟨_, by simp, hv⟩
      | succ i =>
        obtain ⟨v', hget, hv⟩ := ih (by simpa using hg)
        exact ⟨v', by simpa using hget, hv⟩
  intro ihk
  intro m n env env' e v h₀ h₁ h₂
  induction h₂ generalizing m env'
  case var env i v h =>
    obtain ⟨v', hget, happrox⟩ := value_lookup h₁ h
    exists v'
    constructor
    · apply Eval.var
      aesop
    · apply Value.Approx.Indexed.monotone
      · assumption
      · linarith
  case var_rec n' env₁ name i env₁' e₁' v' hget heval ih =>
    have hget_or :
        (∃ env₂' e₂', e₁' ≲(m + n')⟨env₁', env₂'⟩ e₂' ∧
          env'[i]? = some (Object.delayed env₂' e₂')) ∨
        (∃ env₂', env₁' ≲ₑ'(m + n') env₂' ∧
          env'[i]? = some (Object.delayed env₂' e₁')) := by
      apply delayed_lookup h₁; assumption
    cases hget_or
    case inl hget' =>
      obtain ⟨env₂', e₂', h₂, hget'⟩ := hget'
      simp [Expr.Approx.Param.Indexed] at h₂
      obtain ⟨v'', heval', happrox'⟩ := h₂ n' m v' (by linarith) heval
      exists v''
      constructor
      · apply Eval.var_rec
        · exact hget'
        · assumption
      · assumption
    case inr hget' =>
      obtain ⟨env₂, happrox, hget'⟩ := hget'
      obtain ⟨v'', heval', happrox'⟩ := ih m env₂ (by linarith) happrox
      exists v''
      constructor
      · apply Eval.var_rec
        · exact hget'
        · assumption
      · assumption
  case unit =>
    exists Value.unit
    constructor
    · apply Eval.unit
    · apply Value.Approx.Indexed.unit
  case const c =>
    exists Value.const c
    constructor
    · apply Eval.const
    · apply Value.Approx.Indexed.const
  case constr ctr_name =>
    exists Value.constr_app ctr_name []
    constructor
    · apply Eval.constr
    · apply Value.Approx.Indexed.constr_app
      intro k hk
      simp
  case app n n₁ n₂ env env₀ f body arg val val' hn hcl h₂ h₃ ih_f ih_arg ih_body =>
    have : env ≲ₑ'(m + n₂ + 1 + n₁) env' := by
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    obtain ⟨v_f, heval_f, happrox_f⟩ := ih_f (m + n₂ + 1) env' (by linarith) this
    clear this
    have : env ≲ₑ'(m + n₂ + n₁ + 1) env' := by
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    obtain ⟨v_arg, heval_arg, happrox_arg⟩ := ih_arg (m + n₂) env' (by nlinarith) this
    clear this
    invert happrox_f
    case closure cenv cbody ch =>
      have happrox_arg' : val ≲ᵥ(n₂ + m) v_arg := by
        have : m + n₂ = n₂ + m := by linarith
        rw [this] at happrox_arg
        exact happrox_arg
      obtain ⟨v_body, heval_body, happrox_body⟩ := ch n₂ m (by linarith) val v_arg val' happrox_arg' h₃
      exists v_body
      constructor
      · apply Eval.app
        · exact heval_f
        · exact heval_arg
        · exact heval_body
      · assumption
  case constr_app n₁ n₂ env₁ e₁ cname args arg v' hlt _ h₂ h₃ h₄ =>
    obtain ⟨v₁, heval_e₁, happrox_e₁⟩ := h₃ m env' (by linarith) h₁
    have : env₁ ≲ₑ'(m + n₂) env' := by
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    obtain ⟨v₂, heval_arg, happrox_arg⟩ := h₄ m env' (by linarith) this
    invert happrox_e₁
    case constr_app args_rev hargs =>
      exists (Value.constr_app cname (v₂ :: args_rev))
      constructor
      · apply Eval.constr_app
        · exact heval_e₁
        · exact heval_arg
      · apply Value.Approx.Indexed.constr_app
        intro k hk
        constructor
        · apply Value.Approx.Indexed.monotone
          · exact happrox_arg
          · linarith
        · apply hargs
          linarith
  case binop n' env₁ op arg₁ arg₂ i₁ i₂ v₁ v₂ hv₁ hv₂ =>
    obtain ⟨v₁', heval₁, happrox₁⟩ := hv₁ m env' (by linarith) h₁
    obtain ⟨v₂', heval₂, happrox₂⟩ := hv₂ m env' (by linarith) h₁
    invert happrox₁
    invert happrox₂
    exists (Value.const (Constant.int (eval_binop_int op i₁ i₂)))
    constructor
    · apply Eval.binop
      · exact heval₁
      · exact heval₂
    · apply Value.Approx.Indexed.const
  case lambda n' env₁ name body =>
    exists (Value.closure env' body)
    constructor
    · apply Eval.lambda
    · apply Value.Approx.Indexed.closure
      intro n₁ n₂ hlt a₁ a₂ v₁ happrox heval
      have happrox_env : a₁ ∷ env₁ ≲ₑ'(n₁ + n₂) a₂ ∷ env' := by
        constructor
        · constructor
          exact happrox
        · apply Env.Approx.Indexed'.monotone (n₁ := m + n')
          · assumption
          · linarith
      apply ihk (n₁ + n₂ + 1) (by linarith) (m := n₂) (n := n₁)
      · linarith
      · have : n₁ + n₂ = n₂ + n₁ := by linarith
        rw [<- this]
        exact happrox_env
      · exact heval
  case save n' n₁ n₂ env₁ name e₁ e₂ val val' hle ha₁ ha₂ ih₁ ih₂ =>
    have : env₁ ≲ₑ'(m + n₂ + n₁) env' := by
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    obtain ⟨v₁, heval₁, happrox₁⟩ := ih₁ (m + n₂) env' (by linarith) this
    clear this
    have : val ∷ env₁ ≲ₑ'(m + n₂) v₁ ∷ env' := by
      constructor
      · apply Object.Approx.Indexed'.value
        · apply Value.Approx.Indexed.monotone
          · exact happrox₁
          · linarith
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    obtain ⟨v₂, heval₂, happrox₂⟩ := ih₂ m (v₁ ∷ env') (by linarith) this
    exists v₂
    constructor
    · apply Eval.save
      · exact heval₁
      · exact heval₂
    · assumption
  case branch_matches e' n₁ n₁' env₁ name args_rev body val hlt heval_body ih =>
    rcases env' with
      ⟨⟩ | ⟨⟨hd⟩, env'⟩
    case nil =>
      cases h₁
    case cons.value =>
      cases h₁
      case cons h₁ h₂ =>
        cases h₁
        case value h₁ =>
          invert h₁
          case constr_app args_rev' happrox =>
            let args := List.map Object.value args_rev
            let args' := List.map Object.value args_rev'
            have : args ++ env₁ ≲ₑ'(m + n₁') args' ++ env' := by
              apply List.rel_append
              · apply forall₂_map_value
                apply happrox
                linarith
              · apply Env.Approx.Indexed'.monotone
                · assumption
                · linarith
            obtain ⟨v', heval', happrox'⟩ := ih m (args' ++ env') (by linarith) this
            exists v'
            constructor
            · apply Eval.branch_matches
              · exact heval'
            · assumption
    case cons.delayed =>
      cases h₁
      case cons h _ =>
        cases h
  case branch_fails e' n' env₁ name name' args e₂ v₂ hname heval ih =>
    rcases env' with
      ⟨⟩ | ⟨⟨hd⟩, env'⟩
    case nil =>
      cases h₁
    case cons.value =>
      cases h₁
      case cons h₁ h₂ =>
        cases h₁
        case value h₁ =>
          invert h₁
          case constr_app args_rev h =>
            have h₃ : Value.constr_app name args ∷ env₁ ≲ₑ'(m + n') Value.constr_app name args_rev ∷ env' := by
              constructor
              · apply Object.Approx.Indexed'.value
                apply Value.Approx.Indexed.constr_app
                intro k hk
                apply h
                exact hk
              · apply Env.Approx.Indexed'.monotone
                · assumption
                · linarith
            obtain ⟨v', heval', happrox'⟩ := ih m (Value.constr_app name args_rev ∷ env') (by linarith) h₃
            exists v'
            constructor
            · apply Eval.branch_fails
              · exact hname
              · exact heval'
            · assumption
    case cons.delayed =>
      cases h₁
      case cons h _ =>
        cases h
  case recur n₁ n₂ env₁ name body val hn ha₁ ih =>
    let d := Object.delayed env₁ (Expr.recur name body)
    let d' := Object.delayed env' (Expr.recur name body)
    have : d ≲ₒ'(m + n₂) d' := by
      simp [d, d']
      apply Object.Approx.Indexed'.delayed_eq
      apply Env.Approx.Indexed'.monotone
      · assumption
      · linarith
    have : d :: env₁ ≲ₑ'(m + n₂) d' :: env' := by
      apply List.Forall₂.cons
      · assumption
      · apply Env.Approx.Indexed'.monotone
        · assumption
        · linarith
    obtain ⟨v, heval, happrox⟩ := ih m (d' :: env') (by linarith) this
    exists v
    constructor
    · apply Eval.recur
      exact heval
    · assumption

/-! ### Delayed object inversion and environment lookup -/

/--
Inversion lemma for `Object.Approx.Indexed'` on delayed objects.
If `Object.delayed env e` approximates `b` at depth `n`, then either:
* `b = Object.delayed env' e'` with `e ≲(n)⟨env, env'⟩ e'` (delayed case), or
* `b = Object.delayed env' e` with `env ≲ₑ'(n) env'` (delayed_eq case).
-/
lemma Object.Approx.Indexed'.delayed_inv {n env e b}
    (h : Object.delayed env e ≲ₒ'(n) b) :
    (∃ env' e', e ≲(n)⟨env, env'⟩ e' ∧ b = Object.delayed env' e') ∨
    (∃ env', env ≲ₑ'(n) env' ∧ b = Object.delayed env' e) := by
  match h with
  | .delayed h_approx => exact Or.inl ⟨_, _, h_approx, rfl⟩
  | .delayed_eq h_env => exact Or.inr ⟨_, h_env, rfl⟩

/--
Given two related environments `env₁ ≲ₑ'(n) env₂`, if `env₁` has a delayed object
at index `i`, then the corresponding index in `env₂` also holds a delayed object,
and either the expressions or the environments inside are related.
-/
lemma Env.Approx.Indexed'.delayed_1 {n i : Nat} {env₁ env₂ env e}
    (h₁ : env₁ ≲ₑ'(n) env₂)
    (h₂ : env₁[i]? = some (Object.delayed env e)) :
    (∃ env' e', e ≲(n)⟨env, env'⟩ e' ∧ env₂[i]? = some (Object.delayed env' e')) ∨
    (∃ env', env ≲ₑ'(n) env' ∧ env₂[i]? = some (Object.delayed env' e)) := by
  match h₁ with
  | List.Forall₂.nil =>
    simp at h₂
  | @List.Forall₂.cons _ _ _ a b as bs hhead htail =>
    cases i with
    | zero =>
      have ha : a = Object.delayed env e := by
        simpa using h₂
      rcases ha with rfl
      rcases Object.Approx.Indexed'.delayed_inv hhead with
        (⟨env', e', h_approx, rfl⟩ | ⟨env', h_env_approx, rfl⟩)
      · left; refine ⟨env', e', h_approx, ?_⟩; simp
      · right; refine ⟨env', h_env_approx, ?_⟩; simp
    | succ i' =>
      simp at h₂
      have h_rec := Env.Approx.Indexed'.delayed_1 htail h₂
      rcases h_rec with (⟨env', e', h_approx, h_some⟩ | ⟨env', h_env_approx, h_some⟩)
      · left; refine ⟨env', e', h_approx, ?_⟩; simp [h_some]
      · right; refine ⟨env', h_env_approx, ?_⟩; simp [h_some]

/--
If two environments `env₁` and `env₂` are related by `≲ₑ'(n)`, then mapping
`Object.delayed env₁` and `Object.delayed env₂` over any expression list produces
related object lists.
-/
lemma Env.Approx.Indexed'.from_delayed_1 {n env₁ env₂ l} (h : env₁ ≲ₑ'(n) env₂) :
    List.map (Object.delayed env₁) l ≲ₑ'(n) List.map (Object.delayed env₂) l := by
  apply _root_.list_map_forall₂_of_pointwise
  intro e
  exact Object.Approx.Indexed'.delayed_eq h

/-! ### Non-indexed Object.Approx inversion and transitivity -/

/--
If `Object.value v₁` approximates `o₂`, then `o₂` must be `Object.value v₂`
for some `v₂` such that `v₁ ≲ᵥ v₂`.
-/
lemma Object.Approx.value_inv {v₁ o₂} (h : Object.value v₁ ≲ₒ o₂) :
    ∃ v₂, o₂ = Object.value v₂ ∧ v₁ ≲ᵥ v₂ := by
  cases h
  exact ⟨_, rfl, ‹_›⟩

/--
If `Object.delayed env₁ e₁` approximates `o₂`, then `o₂` must be
`Object.delayed env₂ e₂` for some `env₂`, `e₂` such that `e₁ ≲⟨env₁, env₂⟩ e₂`.
-/
lemma Object.Approx.delayed_inv {env₁ e₁ o₂} (h : Object.delayed env₁ e₁ ≲ₒ o₂) :
    ∃ env₂ e₂, o₂ = Object.delayed env₂ e₂ ∧ e₁ ≲⟨env₁, env₂⟩ e₂ := by
  cases h
  exact ⟨_, _, rfl, ‹_›⟩

/--
Lift `Value.Approx.trans` through `Object.value`. If two values are related by
approximation in a chain, then the corresponding value objects are related.
-/
lemma Object.Approx.trans_value {v₁ v₂ v₃} (h₁ : v₁ ≲ᵥ v₂) (h₂ : v₂ ≲ᵥ v₃) :
    Object.Approx (Object.value v₁) (Object.value v₃) :=
  Object.Approx.value (Value.Approx.trans h₁ h₂)

/--
Lift `Expr.Approx.Param.trans` through `Object.delayed`. If two expressions are
related by parameterized approximation in a chain, then the corresponding
delayed objects are related.
-/
lemma Object.Approx.trans_delayed {env₁ env₂ env₃ e₁ e₂ e₃}
    (h₁ : e₁ ≲⟨env₁, env₂⟩ e₂) (h₂ : e₂ ≲⟨env₂, env₃⟩ e₃) :
    Object.Approx (Object.delayed env₁ e₁) (Object.delayed env₃ e₃) :=
  Object.Approx.delayed (Expr.Approx.Param.trans h₁ h₂)

/--
Transitivity of `Object.Approx`. If `o₁ ≲ₒ o₂` and `o₂ ≲ₒ o₃`, then `o₁ ≲ₒ o₃`.
-/
@[trans]
lemma Object.Approx.trans {o₁ o₂ o₃} : o₁ ≲ₒ o₂ → o₂ ≲ₒ o₃ → o₁ ≲ₒ o₃ := by
  intro h₁ h₂
  cases h₁
  case value hval₁ =>
    rcases Object.Approx.value_inv h₂ with ⟨v₃, rfl, hval₂⟩
    exact Object.Approx.trans_value hval₁ hval₂
  case delayed hdel₁ =>
    rcases Object.Approx.delayed_inv h₂ with ⟨env₃, e₃, rfl, hdel₂⟩
    exact Object.Approx.trans_delayed hdel₁ hdel₂

/-! ### Non-indexed Env.Approx lemmas -/

/-- The empty environments are related by `Env.Approx`. -/
lemma Env.Approx.nil : ([] : Env) ≲ₑ ([] : Env) := by
  unfold Env.Approx
  exact List.Forall₂.nil

/-- If the heads of two environments are related by `Object.Approx` and the tails are related
by `Env.Approx`, then the cons of the environments preserves the relation. -/
lemma Env.Approx.cons {a₁ a₂ : Object} {env₁ env₂ : Env}
    (ha : a₁ ≲ₒ a₂) (he : env₁ ≲ₑ env₂) : (a₁ :: env₁) ≲ₑ (a₂ :: env₂) := by
  unfold Env.Approx
  exact List.Forall₂.cons ha he

/-- Decompose an `Env.Approx` relation on cons into the head relation on `Object.Approx`. -/
lemma Env.Approx.head {a₁ a₂ : Object} {env₁ env₂ : Env}
    (h : (a₁ :: env₁) ≲ₑ (a₂ :: env₂)) : a₁ ≲ₒ a₂ := by
  unfold Env.Approx at h
  cases h
  case cons ha _ => exact ha

/-- Decompose an `Env.Approx` relation on cons into the tail relation on `Env.Approx`. -/
lemma Env.Approx.tail {a₁ a₂ : Object} {env₁ env₂ : Env}
    (h : (a₁ :: env₁) ≲ₑ (a₂ :: env₂)) : env₁ ≲ₑ env₂ := by
  unfold Env.Approx at h
  cases h
  case cons _ he => exact he

/-- If two values are related by `Value.Approx` and two environments are related
by `Env.Approx`, then using `cons_value` on them preserves the environment relation. -/
lemma Env.Approx.cons_value {v₁ v₂ : Value} {env₁ env₂ : Env}
    (hv : v₁ ≲ᵥ v₂) (he : env₁ ≲ₑ env₂) : (cons_value v₁ env₁) ≲ₑ (cons_value v₂ env₂) := by
  show (Object.value v₁ :: env₁) ≲ₑ (Object.value v₂ :: env₂)
  apply Env.Approx.cons
  · exact Object.Approx.value hv
  · exact he

/-- If two values are related by `Value.Approx`, then pushing them onto the same environment
preserves the `Env.Approx` relation. -/
lemma Env.Approx.cons_value_1 {v₁ v₂ env} (h : v₁ ≲ᵥ v₂) : v₁ ∷ env ≲ₑ v₂ ∷ env := by
  exact Env.Approx.cons_value h Env.Approx.refl

end Juvix.Core.Main
