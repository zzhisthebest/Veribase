import Capless.Basic
import Capless.CaptureSet
import Capless.Context

/-!
# Basic Lemmas for System Capless

Fundamental helper lemmas about `FinFun` renaming functions from `Capless.Basic` and
`CaptureSet` renaming properties.
-/

namespace Capless

/--
`FinFun.id.ext` is extensionally equal to `FinFun.id`.
-/
theorem FinFun.id_ext {n : Nat} :
    (FinFun.id.ext : FinFun (n+1) (n+1)) = FinFun.id := by
  funext i; cases i using Fin.cases <;> simp [FinFun.ext, FinFun.id]

/-! ## CaptureSet renaming properties -/

/--
Renaming a capture set with `f` then with `g` equals renaming with `g ∘ f`.
This is the functoriality property of `CaptureSet.rename`.
-/
lemma CaptureSet.rename_rename (C : CaptureSet n k) (f : FinFun n n') (g : FinFun n' n'') :
    (C.rename f).rename g = C.rename (g ∘ f) := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 => simp [ih1, ih2]
  | singleton x => rfl
  | csingleton c => rfl

/--
Renaming with `f.ext` after weakening equals weakening after renaming with `f`,
with a singleton `{x=0}` added. This is a key commutation lemma for the `abs` case
of renaming/substitution proofs.
-/
lemma CaptureSet.rename_rename_ext_weaken_union (C : CaptureSet n k) (f : FinFun n n') :
    ((C.weaken ∪ {x=0} : CaptureSet (n+1) k).rename f.ext) = (C.rename f).weaken ∪ {x=0} := by
  have hcomp : f.ext ∘ FinFun.weaken = FinFun.weaken ∘ f := by
    calc
      f.ext ∘ FinFun.weaken = f.ext ∘ Fin.succ := rfl
      _ = (FinFun.ext f) ∘ Fin.succ := rfl
      _ = Fin.succ ∘ f := by rw [FinFun.comp_succ]
      _ = FinFun.weaken ∘ f := rfl
  simp [CaptureSet.weaken, CaptureSet.rename_rename, FinFun.ext_zero, hcomp]

/-! ## FinFun helper lemmas -/

/--
`FinFun.ext` distributes over composition: `f.ext ∘ g.ext = (f ∘ g).ext`.
-/
theorem FinFun.ext_comp_symm {f : FinFun k1 k2} {g : FinFun k k1} :
    f.ext ∘ g.ext = FinFun.ext (f ∘ g) := by
  funext i
  cases i using Fin.cases
  · simp [FinFun.ext]
  · simp [FinFun.ext]

/--
`FinFun.ext` distributes over composition, forward direction:
`FinFun.ext (g ∘ f) = FinFun.ext g ∘ FinFun.ext f`.
-/
theorem FinFun.ext_comp {f : FinFun n n'} {g : FinFun n' n''} :
    FinFun.ext (g ∘ f) = FinFun.ext g ∘ FinFun.ext f :=
  (FinFun.ext_comp_symm (f := g) (g := f)).symm

/--
Weakening of the target domain commutes with composition:
`f.ext ∘ FinFun.weaken = FinFun.weaken ∘ f`.
-/
theorem FinFun.weaken_comp_crename {f : FinFun k k'} :
    f.ext ∘ FinFun.weaken = FinFun.weaken ∘ f := by
  calc
    f.ext ∘ FinFun.weaken = f.ext ∘ Fin.succ := rfl
    _ = Fin.succ ∘ f := by rw [FinFun.comp_succ]
    _ = FinFun.weaken ∘ f := rfl

/-! ## CaptureSet renaming properties -/

/--
Capture-variable renaming composes: `(C.crename g).crename f = C.crename (f ∘ g)`.
This is the functoriality property of `CaptureSet.crename`.
-/
theorem CaptureSet.crename_comp (C : CaptureSet n k)
    {k1 k2 : ℕ} (g : FinFun k k1) (f : FinFun k1 k2) :
    (C.crename g).crename f = C.crename (f ∘ g) := by
  induction C
  case empty => simp [CaptureSet.crename]
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.crename, ih1, ih2]
  case singleton x => simp [CaptureSet.crename]
  case csingleton c => simp [CaptureSet.crename]

/--
Capture-variable renaming with the identity function is the identity:
`C.crename FinFun.id = C`.
-/
theorem CaptureSet.crename_id {C : CaptureSet n k} : C.crename FinFun.id = C := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 => simp [CaptureSet.crename, ih1, ih2]
  | singleton x => rfl
  | csingleton c => simp [CaptureSet.crename, FinFun.id]

/--
Renaming a term-variable singleton capture set does not change it:
`{x=x}.crename f = {x=x}`.
-/
theorem CaptureSet.crename_singleton {x : Fin n} {f : FinFun k k'} :
    ({x=x} : CaptureSet n k).crename f = {x=x} := by
  simp [CaptureSet.crename]

/--
Renaming a capture-variable singleton capture set maps the index:
`{c=c}.crename f = {c=f c}`.
-/
theorem CaptureSet.crename_csingleton {c : Fin k} {f : FinFun k k'} :
    ({c=c} : CaptureSet n k).crename f = {c=f c} := by
  simp [CaptureSet.crename]

/--
Capture-variable renaming distributes over union:
`(C1 ∪ C2).crename f = C1.crename f ∪ C2.crename f`.
-/
theorem CaptureSet.crename_union {C1 C2 : CaptureSet n k} {f : FinFun k k'} :
    (C1 ∪ C2).crename f = C1.crename f ∪ C2.crename f := by
  simp [CaptureSet.crename]

/-! ## CBinding helper lemmas -/

/--
A capture-weakened `CBinding.bound` can never equal a `CBinding.inst`.
This eliminates impossible cases in context inversion proofs
where a `Context.CBound` judgment through `cvar` produces an `inst` result.
-/
theorem CBinding.bound_cweaken_ne_inst {b0 : CBound n k} {C : CaptureSet n (k+1)} :
    (CBinding.bound b0).cweaken ≠ CBinding.inst C := by
  simp [CBinding.cweaken, CBinding.crename]

/--
If a capture-weakened binding equals `inst C`, then the original binding must also be
an `inst`, and `C` is the capture-weakened version of the original capture set.

This generalizes `CBinding.eq_inst_cweaken_inv` by additionally relating `C` to the
original capture set via capture-weakening.
-/
theorem CBinding.eq_inst_of_cweaken_inst {b : CBinding n k} (h : b.cweaken = CBinding.inst C) :
    ∃ C0, b = CBinding.inst C0 ∧ C = C0.cweaken := by
  cases b with
  | bound b0 => simp [CBinding.cweaken, CBinding.crename] at h
  | inst C0 =>
    simp [CBinding.cweaken, CBinding.crename] at h
    -- h : C0.crename FinFun.weaken = C
    exact ⟨C0, rfl, by simpa [CaptureSet.cweaken] using h.symm⟩

end Capless
