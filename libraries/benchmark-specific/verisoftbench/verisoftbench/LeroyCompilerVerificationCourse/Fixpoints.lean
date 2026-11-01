import LeroyCompilerVerificationCourse.Fixpoints

open OrderStruct
open Monotone

universe u

set_option quotPrecheck false

/--
If `iterate β G` is started from a pre-fixpoint `x` (where `le x (G x)`)
and `x` is below any post-fixpoint, then the result is below any
post-fixpoint `z` (where `le (G z) z`).
-/
theorem iterate_le_of_postfix {β : Sort u} [OrderStruct β] {G : β → β} [Monotone β G]
    (x z : β) (PRE : le x (G x)) (SMALL : ∀ w, le (G w) w → le x w) (hz : le (G z) z) :
    le (iterate β G x PRE SMALL) z := by
  refine iterate.induct (α := β) (F := G)
    (motive := λ x' PRE' SMALL' => le (iterate β G x' PRE' SMALL') z)
    ?case1 ?case2 x PRE SMALL
  · intro x' PRE' SMALL' h_eq
    rw [iterate.eq_1 (α := β) (F := G) (x := x') (PRE := PRE') (SMALL := SMALL')]
    rw [if_pos h_eq]
    exact SMALL' z hz
  · intro x' PRE' SMALL' h_eq ih
    rw [iterate.eq_1 (α := β) (F := G) (x := x') (PRE := PRE') (SMALL := SMALL')]
    rw [if_neg h_eq]
    exact ih

/--
If `le x y` and `beq x y = false`, then `gt y x`.
This derives the strict (well-founded) order from the non-strict order
and the boolean equality test.
-/
theorem le_beq_false_imp_gt {α : Sort u} [OrderStruct α] {x y : α}
    (hle : le x y) (hbeq : beq x y = false) : gt y x := by
  constructor
  · exact hle
  · exact beq_false' x y hbeq

/--
Monotonicity combined with transitivity: if `le x z` and `le (G z) z`,
then `le (G x) z` for a monotone `G`.
-/
theorem mon_le_trans {α : Sort u} [OrderStruct α] {G : α → α} [Monotone α G] {x z : α}
    (hxz : le x z) (hGz : le (G z) z) : le (G x) z :=
  le_trans (G x) (G z) z (F_mon hxz) hGz

/-- The result of iterating `G` from a pre-fixpoint `x` satisfies `beq` equality with `G` applied to it. -/
theorem iterate_is_beq_fixpoint {β : Sort u} [OrderStruct β] (G : β → β) [Monotone β G] (x : β)
    (PRE : OrderStruct.le x (G x)) (SMALL : ∀ z, OrderStruct.le (G z) z → OrderStruct.le x z) :
    OrderStruct.beq (iterate β G x PRE SMALL) (G (iterate β G x PRE SMALL)) = true := by
  fun_induction iterate
  case case1 x' PRE' SMALL' isTrue =>
    assumption
  case case2 ih =>
    exact ih

/-- The result of iterating `G` from a pre-fixpoint `x` satisfies `eq` equality with `G` applied to it. -/
theorem iterate_is_eq_fixpoint {β : Sort u} [OrderStruct β] (G : β → β) [Monotone β G] (x : β)
    (PRE : OrderStruct.le x (G x)) (SMALL : ∀ z, OrderStruct.le (G z) z → OrderStruct.le x z) :
    OrderStruct.eq (iterate β G x PRE SMALL) (G (iterate β G x PRE SMALL)) := by
  apply beq_true'
  apply iterate_is_beq_fixpoint

/-- `fixpoint_join Init F` is a `beq`-fixpoint of `Join Init (F ·)`. -/
theorem fixpoint_join_is_beq_fixpoint (Init : Store) (F : Store → Store) [Monotone Store F] :
    OrderStruct.beq (fixpoint_join Init F) (Join Init (F (fixpoint_join Init F))) = true := by
  unfold fixpoint_join
  apply iterate_is_beq_fixpoint

/-- `fixpoint_join Init F` is a fixpoint of `Join Init (F ·)` under `OrderStruct.eq`. -/
theorem fixpoint_join_is_eq_fixpoint (Init : Store) (F : Store → Store) [Monotone Store F] :
    OrderStruct.eq (fixpoint_join Init F) (Join Init (F (fixpoint_join Init F))) := by
  apply beq_true'
  exact fixpoint_join_is_beq_fixpoint Init F

theorem fixpoint_join_eq_1 (Init : Store) (F : Store → Store) [Monotone Store F] :
    Eq' (Join Init (F (fixpoint_join Init F))) (fixpoint_join Init F) := by
  have hbeq := fixpoint_join_is_beq_fixpoint Init F
  have heq' : Eq' (fixpoint_join Init F) (Join Init (F (fixpoint_join Init F))) := by
    apply beq_true' _ _ hbeq
  apply Eq'_sym
  exact heq'

/-- `fixpoint_join Init F` is below any `S` such that `Join Init (F S) ≤ S`.
  This states that `fixpoint_join` computes the least post-fixpoint. -/
theorem fixpoint_join_smallest (Init : Store) (F : Store → Store) [Monotone Store F] (S : Store)
    (hpost : Le (Join Init (F S)) S) : Le (fixpoint_join Init F) S := by
  have hpre : Le Init (Join Init (F Init)) := by
    intro x n hn
    exact ((Join_characterization Init (F Init) x n).mp hn).1
  have hsmall : ∀ (z : Store), Le (Join Init (F z)) z → Le Init z := by
    intro z hz x n hn
    exact ((Join_characterization Init (F z) x n).mp (hz x n hn)).1
  have hiter : Le (iterate Store (fun x => Join Init (F x)) Init hpre hsmall) S :=
    iterate_le_of_postfix (G := fun x => Join Init (F x)) Init S hpre hsmall hpost
  exact hiter
