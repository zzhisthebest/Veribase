import VCVio.OracleComp.DistSemantics.EvalDist
import VCVio.OracleComp.DistSemantics.Alternative
import VCVio.OracleComp.QueryBound
import VCVio.OracleComp.Coercions.SubSpec
import verisoftbench.Common.Topology.ENNReal
import verisoftbench.Common.Option

set_option quotPrecheck false
open OracleSpec OracleComp BigOperators ENNReal

universe u v w w'
variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α β γ : Type w}
variable [MonadLift (OracleQuery spec) (OracleQuery superSpec)]

lemma prod_mk_injective2 {α β : Type v} :
    Function.Injective2 (Prod.mk : α → β → α × β) :=
  λ x1 y1 x2 y2 h ↦ by
    have h_eq := Prod.mk.inj h
    exact ⟨h_eq.1, h_eq.2⟩

/-- If two predicates agree on the support of a PMF over `Option α`, then the
intersection of their `Option.some` images with the support are equal. -/
lemma some_image_inter_support_eq_of_event_iff {α : Type w} {μ : PMF (Option α)}
    {p q : α → Prop} (h : ∀ x, some x ∈ μ.support → (p x ↔ q x)) :
    (Option.some '' {x | p x}) ∩ μ.support = (Option.some '' {x | q x}) ∩ μ.support := by
  ext y; constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩; exact ⟨⟨x, ((h x hy).mp hx), rfl⟩, hy⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩; exact ⟨⟨x, ((h x hy).mpr hx), rfl⟩, hy⟩

namespace OracleComp

lemma simulateQ_query [AlternativeMonad m] [LawfulMonad m] [LawfulAlternative m]
    (so : QueryImpl spec m) (q : OracleQuery spec α) :
    simulateQ so (q : OracleComp spec α) = so.impl q := by
  unfold simulateQ
  have hrun : ((q : OracleComp spec α)).run = FreeMonad.roll q (λ u : α => pure (some u)) := by
    calc
      ((q : OracleComp spec α)).run = (OptionT.lift (FreeMonad.lift q)).run := rfl
      _ = (do let a ← FreeMonad.lift q; pure (some a)) := by rw [OptionT.run_lift]
      _ = FreeMonad.lift q >>= (λ a => pure (some a)) := rfl
      _ = FreeMonad.bind (FreeMonad.roll q FreeMonad.pure) (λ a => pure (some a)) := by
        rw [FreeMonad.lift, FreeMonad.monad_bind_def]
      _ = FreeMonad.roll q (λ u : α => pure (some u)) := by
        simp [FreeMonad.bind_roll, FreeMonad.bind_pure]
  rw [hrun]
  simp [FreeMonad.mapM]

/-- `evalDist` on a query lifted via `MonadLift` from `spec` to `superSpec` equals
`evalDist` on the original query in `spec`. Both reduce to the uniform distribution. -/
lemma evalDist_liftM_query [spec.FiniteRange] [superSpec.FiniteRange] [Fintype α] [Nonempty α]
    (q : OracleQuery spec α) :
    evalDist (liftM q : OracleComp superSpec α) = evalDist (q : OracleComp spec α) := by
  rw [OracleSpec.SubSpec.evalDist_liftM (q := q), OracleComp.evalDist_liftM (q := q)]

/-- `evalDist` is invariant under `liftComp`, i.e., lifting a computation to a superset of oracles
preserves its output distribution under uniformly random oracle responses. -/
@[simp]
lemma evalDist_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
    (oa : OracleComp spec α) : evalDist (liftComp oa superSpec) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [liftComp_pure, evalDist_pure]
  | failure => simp [liftComp_failure, evalDist_failure]
  | query_bind i t oa ih =>
    rw [liftComp_bind superSpec (liftM (query i t) : OracleComp spec (spec.range i)) oa]
    rw [evalDist_bind (liftComp (liftM (query i t) : OracleComp spec (spec.range i)) superSpec)
        (λ x => liftComp (oa x) superSpec),
      evalDist_bind (liftM (query i t) : OracleComp spec (spec.range i)) oa]
    unfold liftComp
    rw [simulateQ_query (m := OracleComp superSpec) ⟨liftM⟩ (OracleQuery.query i t)]
    rw [evalDist_liftM_query (spec := spec) (superSpec := superSpec)
      (q := OracleQuery.query i t)]
    congr
    funext x
    simp
    exact ih x

lemma some_mem_evalDist_support_iff_probOutput_ne_zero [spec.FiniteRange]
    (oa : OracleComp spec α) (x : α) :
    some x ∈ ((evalDist oa).run).support ↔ [= x | oa] ≠ 0 := by
  simp [probOutput]

lemma probOutput_ne_zero_iff_mem_support [spec.FiniteRange] {oa : OracleComp spec α} {x : α} :
    [= x | oa] ≠ 0 ↔ x ∈ oa.support := by
  rw [← not_iff_not, not_ne_iff, probOutput_eq_zero_iff]

/-- The product of two `probOutput` values is zero iff at least one argument is not in
the support. -/
lemma probOutput_mul_eq_zero_iff [spec.FiniteRange] (oa : OracleComp spec α) (ob : OracleComp spec β)
    (x : α) (y : β) : [= x | oa] * [= y | ob] = 0 ↔ x ∉ oa.support ∨ y ∉ ob.support := by
  simp [mul_eq_zero, probOutput_eq_zero_iff]

lemma probEvent_congr'_1 {ι' : Type v} {spec' : OracleSpec ι'} [spec.FiniteRange] [spec'.FiniteRange]
    {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
    (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  let μ := (evalDist oa).run
  have hμ : (evalDist oa).run = (evalDist oa').run := by rw [h2]
  have h_supp_cond : ∀ x, some x ∈ μ.support → (p x ↔ q x) := by
    intro x hx_some_supp
    have hx_prob_ne : [= x | oa] ≠ 0 :=
      ((some_mem_evalDist_support_iff_probOutput_ne_zero oa x).mp hx_some_supp)
    have hx_supp_oa : x ∈ oa.support :=
      (probOutput_ne_zero_iff_mem_support.mp hx_prob_ne)
    have hx_prob'_ne : [= x | oa'] ≠ 0 :=
      ((some_mem_evalDist_support_iff_probOutput_ne_zero oa' x).mp (by
        simpa [μ, hμ] using hx_some_supp))
    have hx_supp_oa' : x ∈ oa'.support :=
      (probOutput_ne_zero_iff_mem_support.mp hx_prob'_ne)
    exact h1 x hx_supp_oa hx_supp_oa'
  calc
    [p | oa] = μ.toOuterMeasure (Option.some '' {x | p x}) := rfl
    _ = μ.toOuterMeasure (Option.some '' {x | q x}) := by
      rw [PMF.toOuterMeasure_apply_eq_of_inter_support_eq (p := μ)
        (some_image_inter_support_eq_of_event_iff h_supp_cond)]
    _ = [q | oa'] := by
      dsimp [probEvent, μ]
      rw [hμ]

@[simp]
lemma support_pure {sp : OracleSpec ι} {a : Type u} (a' : a) :
    (pure a' : OracleComp sp a).support = {a'} := by
  simp [OracleComp.support]

lemma mem_support_orElse_return_iff {sp : OracleSpec ι} [DecidableEq ι]
    {a : Type u} (oa : OracleComp sp a) (a0 x : a) :
    x ∈ (oa <|> return a0).support ↔ x ∈ oa.support ∨ (¬ oa.neverFails ∧ x = a0) := by
  classical
    rw [support_orElse, support_pure]
    by_cases hnf : oa.neverFails
    · simp [hnf]
    · simp [hnf, or_comm]

lemma probFailure_orElse_return {sp : OracleSpec ι} [DecidableEq ι]
    {a : Type u} [sp.FiniteRange] (oa : OracleComp sp a) (a0 : a) :
    [⊥ | oa <|> return a0] = 0 := by
  rw [probFailure_orElse, probFailure_pure, mul_zero]

lemma isQueryBound_iff_probEvent_1 {sp : OracleSpec ι} [DecidableEq ι]
    {a : Type u} [sp.FiniteRange]
    {oa : OracleComp sp a} {qb : ι → ℕ} :
    IsQueryBound oa qb ↔
      (let inner : OracleComp sp (QueryCount sp) :=
        (Prod.snd : a × QueryCount sp → QueryCount sp) <$>
          (simulateQ countingOracle oa).run <|> pure (0 : QueryCount sp)
      probEvent inner (· ≤ qb)) = 1 := by
  classical
    rw [isQueryBound_def]
    have h_probEvent_iff := probEvent_eq_one_iff
      (oa := (Prod.snd : a × QueryCount sp → QueryCount sp) <$>
        (simulateQ countingOracle oa).run <|> pure (0 : QueryCount sp))
      (p := (· ≤ qb))
    constructor
    · intro h
      rw [h_probEvent_iff]
      constructor
      · rw [probFailure_orElse_return]
      · intro x hx
        rw [mem_support_orElse_return_iff] at hx
        rcases hx with (hx | ⟨_, hx⟩)
        · exact h x hx
        · subst x; intro i; exact Nat.zero_le (qb i)
    · intro h
      rw [h_probEvent_iff] at h
      obtain ⟨_, h_all⟩ := h
      intro qc hqc
      apply h_all
      rw [mem_support_orElse_return_iff]
      left; exact hqc

/-- If every output `x` has the same probability `c` under `oa`, then the probability of event `p`
is `c` times the cardinality of `p`'s support. -/
lemma probEvent_eq_card_mul_of_const_probOutput [spec.FiniteRange] [Fintype α]
    (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] (c : ℝ≥0∞)
    (h : ∀ x, [= x | oa] = c) : [p | oa] = (Finset.univ.filter p).card * c := by
  rw [probEvent_eq_sum_fintype_ite]
  simp [h]

/-- Probability of an event `p` under the uniform distribution on `Fin (n + 1)`. -/
@[simp]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    [p | $[0..n]] = (Finset.univ.filter p).card * (n + 1 : ℝ≥0∞)⁻¹ := by
  apply probEvent_eq_card_mul_of_const_probOutput
  intro x
  simp

/-!
## Failure probability bounds
-/

/-- The failure probability of any computation is at most 1. -/
lemma probFailure_le_one [spec.FiniteRange] (oa : OracleComp spec α) : [⊥ | oa] ≤ 1 :=
  le_of_not_gt (not_one_lt_probFailure (oa := oa))

/-- The failure probability of any computation is finite (not ∞). -/
lemma probFailure_ne_top [spec.FiniteRange] (oa : OracleComp spec α) : [⊥ | oa] ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probFailure_le_one oa)

/-!
## Tsum identities for probability outputs
-/

/-- The sum of `probOutput` over the support of a computation equals the sum over the whole type.
This is because outputs not in the support have zero probability. -/
lemma tsum_probOutput_support_eq_tsum_probOutput [spec.FiniteRange] (oa : OracleComp spec α) :
    ∑' x : oa.support, [= (x : α) | oa] = ∑' x : α, [= x | oa] := by
  calc
    ∑' x : oa.support, [= (x : α) | oa] = ∑' x : α,
        (oa.support : Set α).indicator ([= · | oa]) x := by
      rw [tsum_subtype]
    _ = ∑' x : α, [= x | oa] := by
      refine tsum_congr fun x => ?_
      by_cases hx : x ∈ oa.support
      · simp [hx]
      · have hz : [= x | oa] = 0 := by
          rw [probOutput_eq_zero_iff]
          exact hx
        simp [hx, hz, Set.indicator_of_notMem]

/-- The total sum of output probabilities equals `1` minus the failure probability. -/
lemma tsum_probOutput_eq_one_sub_probFailure [spec.FiniteRange] (oa : OracleComp spec α) :
    ∑' x : α, [= x | oa] = 1 - [⊥ | oa] := by
  have htotal := probFailure_add_tsum_probOutput oa
  have hp_ne_top : [⊥ | oa] ≠ ∞ := probFailure_ne_top oa
  calc
    ∑' x : α, [= x | oa] = ([⊥ | oa] + ∑' x : α, [= x | oa]) - [⊥ | oa] :=
      (ENNReal.add_sub_cancel_left
        (a := [⊥ | oa]) (b := ∑' x : α, [= x | oa]) hp_ne_top).symm
    _ = 1 - [⊥ | oa] := by rw [htotal]

/-!
## Bind probability identities
-/

/-- When a continuation `ob` has constant failure probability `r` for all possible inputs,
the failure probability of the bind is `[⊥ | oa] + r - [⊥ | oa] * r`.
Requires `Nonempty α` so that `r` is determined by a concrete `ob x`. -/
lemma probFailure_bind_of_const [spec.FiniteRange] [Nonempty α]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (r : ℝ≥0∞)
    (h : ∀ x, [⊥ | ob x] = r) :
    [⊥ | oa >>= ob] = [⊥ | oa] + r - [⊥ | oa] * r := by
  set p := [⊥ | oa] with hp_def
  have hp_ne_top : p ≠ ∞ := by
    rw [hp_def]
    exact probFailure_ne_top oa
  have hr_ne_top : r ≠ ∞ := by
    let x : α := Classical.arbitrary _
    rw [← h x]
    exact probFailure_ne_top (ob x)
  have hp_le_one : p ≤ 1 := by
    rw [hp_def]
    exact probFailure_le_one oa
  have hr_le_one : r ≤ 1 := by
    let x : α := Classical.arbitrary _
    rw [← h x]
    exact probFailure_le_one (ob x)
  have hbind_total := probFailure_add_tsum_probOutput (oa >>= ob)
  have htsum_out : ∑' y : β, [= y | oa >>= ob] = (1 - r) * (1 - p) := by
    calc
      ∑' y : β, [= y | oa >>= ob] =
          ∑' y : β, ∑' x : oa.support, [= x | oa] * [= y | ob x] := by
        simp_rw [probOutput_bind_eq_tsum_subtype]
      _ = ∑' x : oa.support, ∑' y : β, [= x | oa] * [= y | ob x] := by
        rw [ENNReal.tsum_comm]
      _ = ∑' x : oa.support, [= x | oa] * (∑' y : β, [= y | ob x]) := by
        simp_rw [ENNReal.tsum_mul_left]
      _ = ∑' x : oa.support, [= x | oa] * (1 - [⊥ | ob x]) := by
        refine tsum_congr fun x => ?_
        rw [tsum_probOutput_eq_one_sub_probFailure (ob x)]
      _ = ∑' x : oa.support, [= x | oa] * (1 - r) := by
        refine tsum_congr fun x => ?_
        rw [h x]
      _ = (1 - r) * (∑' x : oa.support, [= x | oa]) := by
        rw [ENNReal.tsum_mul_right, mul_comm]
      _ = (1 - r) * (∑' x : α, [= x | oa]) := by
        rw [tsum_probOutput_support_eq_tsum_probOutput oa]
      _ = (1 - r) * (1 - [⊥ | oa]) := by
        rw [tsum_probOutput_eq_one_sub_probFailure oa]
      _ = (1 - r) * (1 - p) := by rw [hp_def]
  have hsum_fin' : ∑' y : β, [= y | oa >>= ob] ≠ ∞ := by
    rw [htsum_out]
    exact ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
      (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have hpf : [⊥ | oa >>= ob] = 1 - ∑' y : β, [= y | oa >>= ob] := by
    calc
      [⊥ | oa >>= ob] = ([⊥ | oa >>= ob] + ∑' y : β, [= y | oa >>= ob]) -
          ∑' y : β, [= y | oa >>= ob] :=
        (ENNReal.add_sub_cancel_right
          (a := [⊥ | oa >>= ob]) (b := ∑' y : β, [= y | oa >>= ob]) hsum_fin').symm
      _ = 1 - ∑' y : β, [= y | oa >>= ob] := by rw [hbind_total]
  rw [hp_def, hpf, htsum_out]
  exact one_sub_mul_sub_eq_add_sub_mul p r hp_ne_top hr_ne_top hp_le_one hr_le_one

/-- `f <$> oa <*> ob = f.uncurry <$> (Prod.mk <$> oa <*> ob)` -- a functor identity
for two-argument sequential application. -/
lemma seq_map_uncurry_prod_mk (f : α → β → γ) (oa : OracleComp spec α) (ob : OracleComp spec β) :
    f <$> oa <*> ob = f.uncurry <$> (Prod.mk <$> oa <*> ob) := by
  simp [functor_norm]
  apply congrArg (λ (g : α → β → γ) => g <$> oa <*> ob)
  ext a b; rfl

/-- Probability of event `p` after mapping `g` equals probability of `p ∘ g` on the original
computation. -/
lemma probEvent_map_eq [spec.FiniteRange] (g : α → β) (comp : OracleComp spec α) (p : β → Prop) :
    [p | g <$> comp] = [p ∘ g | comp] := by
  dsimp [probEvent]
  rw [evalDist_map, OptionT.run_map]
  let d : PMF (Option α) := (evalDist comp).run
  have h_map : Option.map g <$> d = PMF.map (Option.map g) d := rfl
  rw [h_map, PMF.toOuterMeasure_map_apply, option_map_preimage_some_image]
  rfl

/-- Probability of event `p` under `f <$> oa <*> ob` equals probability of `p ∘ f.uncurry` under
`Prod.mk <$> oa <*> ob`. -/
lemma probEvent_seq_map_eq_probEvent_comp_uncurry [spec.FiniteRange]
    (f : α → β → γ) (oa : OracleComp spec α) (ob : OracleComp spec β) (p : γ → Prop) :
    [p | f <$> oa <*> ob] =
      [p ∘ f.uncurry | Prod.mk <$> oa <*> ob] := by
  calc
    [p | f <$> oa <*> ob]
        = [p | f.uncurry <$> (Prod.mk <$> oa <*> ob)] := by rw [seq_map_uncurry_prod_mk f oa ob]
    _ = [p ∘ f.uncurry | Prod.mk <$> oa <*> ob] := by rw [probEvent_map_eq]

/-!
## Injectivity of `OracleComp.lift`
-/

variable {α' β' : Type v}

/-- `OracleComp.lift` is injective: if two lifted queries produce equal computations,
then the underlying queries are equal. -/
lemma lift_injective (q q' : OracleQuery spec α') (h : OracleComp.lift q = OracleComp.lift q') :
    q = q' := by
  injection h

/-- Congruence for `OracleComp.lift`: equal queries lift to equal computations. -/
lemma lift_congrArg (q q' : OracleQuery spec α') (h : q = q') :
    OracleComp.lift q = OracleComp.lift q' := by
  subst h; rfl

/-- Equality of lifted queries as computations is equivalent to equality of the
underlying queries. -/
@[simp]
lemma lift_inj (q q' : OracleQuery spec α') :
    OracleComp.lift q = OracleComp.lift q' ↔ q = q' := by
  constructor
  · exact lift_injective q q'
  · exact lift_congrArg q q'

lemma liftM_injective (q q' : OracleQuery spec α') (h : (q : OracleComp spec α') = q') : q = q' :=
  lift_injective q q' h

lemma liftM_congrArg (q q' : OracleQuery spec α') (h : q = q') : (q : OracleComp spec α') = q' :=
  lift_congrArg q q' h

@[simp]
lemma liftM_inj_1 (q q' : OracleQuery spec α') : (q : OracleComp spec α') = q' ↔ q = q' :=
  lift_inj q q'

end OracleComp
