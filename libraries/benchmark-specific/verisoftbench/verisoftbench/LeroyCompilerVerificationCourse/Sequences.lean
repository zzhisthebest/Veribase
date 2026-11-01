import LeroyCompilerVerificationCourse.Sequences

set_option quotPrecheck false

/--
`star R` is transitive: if `star R a b` and `star R b c`, then `star R a c`.
-/
theorem star_trans {R : α → α → Prop} {a b : α} (hab : star R a b) : ∀ {c : α}, star R b c → star R a c := by
  induction hab with
  | star_refl _ => intro c hbc; exact hbc
  | star_step h h_star ih =>
    intro c hbc
    exact star.star_step h (ih hbc)

/--
If `R` is a subrelation of `S` (i.e., `∀ a b, R a b → S a b`), then `star R a b` implies `star S a b`.
-/
theorem star_map {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) {a b : α}
    (hstar : star R a b) : star S a b := by
  induction hstar with
  | star_refl x => exact star.star_refl x
  | star_step hstep hrest ih =>
    exact star.star_step (h _ _ hstep) ih
