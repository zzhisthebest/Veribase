import ExprEval.Expr

/-!
# Generic `StepStar` theorems

Theorems about `StepStar` (the reflexive-transitive closure of a step relation)
that are independent of any particular expression language.
-/

/-- Concatenate two `StepStar` derivations. -/
theorem stepstar_concat (V : Type) {ExprType : Type} {Step : StepKind V ExprType} (val : V → Int) {a b c : ExprType}
    (h1 : StepStar (V := V) (ExprType := ExprType) (Step := Step) val a b)
    (h2 : StepStar (V := V) (ExprType := ExprType) (Step := Step) val b c) :
    StepStar (V := V) (ExprType := ExprType) (Step := Step) val a c := by
  induction h1
  · exact h2
  · case trans a' b' c' hstep hstar ih =>
    apply StepStar.trans (V := V) (ExprType := ExprType) (Step := Step) a' b' c hstep
    exact ih h2

/-- Map a `StepStar` derivation across different step relations. -/
theorem stepstar_map_cross (V : Type) {ExprType1 ExprType2 : Type}
    {Step1 : StepKind V ExprType1} {Step2 : StepKind V ExprType2}
    (val : V → Int) {a b : ExprType1} (f : ExprType1 → ExprType2)
    (hmap : ∀ {x y : ExprType1}, Step1 val x y → Step2 val (f x) (f y))
    (h : StepStar (V := V) (ExprType := ExprType1) (Step := Step1) val a b) :
    StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f a) (f b) := by
  induction h
  · apply StepStar.refl (V := V) (ExprType := ExprType2) (Step := Step2) val
  · case trans a' b' c' hstep hstar ih =>
    apply StepStar.trans (V := V) (ExprType := ExprType2) (Step := Step2) (f a') (f b') (f c')
    · exact hmap hstep
    · exact ih

/-- Map a `StepStar` derivation across the same step relation. -/
theorem stepstar_map (V : Type) {ExprType : Type} {Step : StepKind V ExprType} (val : V → Int) {a b : ExprType}
    (f : ExprType → ExprType) (hmap : ∀ {x y : ExprType}, Step val x y → Step val (f x) (f y))
    (h : StepStar (V := V) (ExprType := ExprType) (Step := Step) val a b) :
    StepStar (V := V) (ExprType := ExprType) (Step := Step) val (f a) (f b) :=
  stepstar_map_cross V val f hmap h

/-- Lift a single step to a `StepStar` derivation. -/
theorem from_step (V : Type) {ExprType : Type} {Step : StepKind V ExprType} (val : V → Int) {a b : ExprType}
    (h : Step val a b) : StepStar (V := V) (ExprType := ExprType) (Step := Step) val a b :=
  StepStar.trans (V := V) (ExprType := ExprType) (Step := Step) a b b h
    (StepStar.refl (V := V) (ExprType := ExprType) (Step := Step) val b)

/-- Reduce a binary operation by stepping both subexpressions, then applying a final step. -/
theorem stepstar_binary_op (V : Type) {ExprType1 ExprType2 : Type}
    {Step1 : StepKind V ExprType1} {Step2 : StepKind V ExprType2} (val : V → Int)
    {l r : ExprType1} {lc rc : ExprType1} {target : ExprType2}
    (f : ExprType1 → ExprType1 → ExprType2)
    (hmap_left : ∀ {x y : ExprType1}, Step1 val x y → Step2 val (f x r) (f y r))
    (hmap_right : ∀ {x y : ExprType1}, Step1 val x y → Step2 val (f lc x) (f lc y))
    (hl : StepStar (V := V) (ExprType := ExprType1) (Step := Step1) val l lc)
    (hr : StepStar (V := V) (ExprType := ExprType1) (Step := Step1) val r rc)
    (hfinal : StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f lc rc) target) :
    StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f l r) target := by
  have h1 : StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f l r) (f lc r) :=
    stepstar_map_cross V val (fun x => f x r) hmap_left hl
  have h2 : StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f lc r) (f lc rc) :=
    stepstar_map_cross V val (fun x => f lc x) hmap_right hr
  have h12 : StepStar (V := V) (ExprType := ExprType2) (Step := Step2) val (f l r) (f lc rc) :=
    stepstar_concat V val h1 h2
  exact stepstar_concat V val h12 hfinal

/-- Reduce a unary operation by stepping the subexpression, then applying a final step. -/
theorem stepstar_unary_op (V : Type) {ExprType : Type} {Step : StepKind V ExprType} (val : V → Int)
    {e ec target : ExprType}
    (f : ExprType → ExprType)
    (hmap : ∀ {x y : ExprType}, Step val x y → Step val (f x) (f y))
    (hstar : StepStar (V := V) (ExprType := ExprType) (Step := Step) val e ec)
    (hfinal : StepStar (V := V) (ExprType := ExprType) (Step := Step) val (f ec) target) :
    StepStar (V := V) (ExprType := ExprType) (Step := Step) val (f e) target := by
  have h1 : StepStar (V := V) (ExprType := ExprType) (Step := Step) val (f e) (f ec) :=
    stepstar_map V val f hmap hstar
  exact stepstar_concat V val h1 hfinal
