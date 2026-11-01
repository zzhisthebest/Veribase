import IntroEffects.Eval

/-! Lemmas about `evalFuel` and the small-step semantics (`⇢` / `⇢⋆`), harvested from solved training problems. -/

/--
`evalFuel` returns `some (.ret v)` for any fuel `n+1 ≥ 1`
when the computation is already a `.ret v`.
-/
theorem evalFuel_succ_ret (v : Value) (n : Nat) : evalFuel (n + 1) (.ret v) = some (.ret v) := by
  grind [evalFuel]

/--
There exists some fuel amount for which `evalFuel` returns
`some (.ret v)` when the computation is already a `.ret v`.
-/
theorem evalFuel_exists_ret (v : Value) : ∃ n, evalFuel n (.ret v) = some (.ret v) := by
  exact ⟨1, evalFuel_succ_ret v 0⟩

/--
If `c₁ ⇢ c₂` and `evalFuel n c₂ = some r`,
then `evalFuel (n + 1) c₁ = some r`.
-/
theorem evalFuel_step_some {c₁ c₂ r : Computation} {n : Nat}
    (hStep : c₁ ⤳ c₂) (hFuel : evalFuel n c₂ = some r) : evalFuel (n + 1) c₁ = some r := by
  rw [evalFuel_step hStep, hFuel]

/--
If `c₁ ⇢ c₂` and there exists `n` with `evalFuel n c₂ = some r`,
then there exists `m` with `evalFuel m c₁ = some r`.
-/
theorem evalFuel_step_exists {c₁ c₂ r : Computation}
    (hStep : c₁ ⤳ c₂) (h : ∃ n, evalFuel n c₂ = some r) : ∃ n, evalFuel n c₁ = some r := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, evalFuel_step_some hStep hn⟩

/--
If `c ⇢⋆ r` and `evalFuel` reaches `r'` starting from `r`,
then `evalFuel` reaches `r'` starting from `c`.
-/
theorem evalFuel_exists_of_stepStar {c r r' : Computation}
    (h : c ⤳⋆ r) (hFuel : ∃ n, evalFuel n r = some r') : ∃ n, evalFuel n c = some r' := by
  induction h with
  | refl r => exact hFuel
  | trans hStep _ ih =>
    apply evalFuel_step_exists hStep
    exact ih hFuel

/--
If `c ⇢⋆ .ret v`, then `evalFuel` eventually reaches `.ret v`.
-/
theorem evalFuel_ret_of_stepStar {c : Computation} {v : Value}
    (h : c ⤳⋆ .ret v) : ∃ n, evalFuel n c = some (.ret v) :=
  evalFuel_exists_of_stepStar h (evalFuel_exists_ret v)
