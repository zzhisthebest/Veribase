import Capless.Type.Renaming
import Capless.Type.Basic
import Capless.CaptureSet
import Capless.Context
import Capless.Term
import verisoftbench.Capless.Basic

/-!
# Basic Properties of Renaming

Identity properties for the `trename` operation on System Capless types.

Note: `CType.trename_id` and `EType.trename_id` are already declared in
`Capless.Type.Basic`. This file adds the missing `SType.trename_id` and
commutation lemmas between renaming operations.
-/

namespace Capless

/-- Renaming with the identity function is the identity on `SType`. -/
theorem SType.trename_id {n m k : Nat} : (S : SType n m k) → S.trename FinFun.id = S
  | SType.top => rfl
  | SType.tvar X => by simp [SType.trename, FinFun.id]
  | SType.forall E1 E2 => by
      simp [SType.trename, CType.trename_id, EType.trename_id]
  | SType.tforall S E => by
      simp [SType.trename, SType.trename_id S, FinFun.id_ext, EType.trename_id]
  | SType.cforall B E => by
      simp [SType.trename, EType.trename_id]
  | SType.box T => by
      simp [SType.trename, CType.trename_id]
  | SType.label S => by
      simp [SType.trename, SType.trename_id S]

/-! ## rename and creaname commute -/

/--
`CaptureSet.rename` and `CaptureSet.crename` commute.
-/
theorem CaptureSet.rename_crename_comm {C : CaptureSet n k}
    {g : FinFun n n'} {f : FinFun k k'} :
    (C.rename g).crename f = (C.crename f).rename g := by
  induction C
  case empty => simp [CaptureSet.rename, CaptureSet.crename]
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.rename, CaptureSet.crename, ih1, ih2]
  case singleton x => simp [CaptureSet.rename, CaptureSet.crename]
  case csingleton c => simp [CaptureSet.rename, CaptureSet.crename]

-- `rename` and `crename` commute for `EType`, `CType`, and `SType`.

/-- `rename` and `crename` commute for `EType`. -/
theorem EType.rename_crename_comm {n m k n' k' : ℕ}
  (E : EType n m k) (g : FinFun n n') (f : FinFun k k') :
  (E.rename g).crename f = (E.crename f).rename g := by
  set_option maxHeartbeats 0 in
    have proof_CBound_rename_crename_comm {k k' n n' : Nat} (B : CBound n k)
        (g : FinFun n n') (f : FinFun k k') :
        (B.rename g).crename f = (B.crename f).rename g := by
      cases B <;> simp [CBound.rename, CBound.crename, CaptureSet.rename_crename_comm]
    let rec proof_SType_rename_crename_comm {n m k n' k' : ℕ}
      (S : SType n m k) (g : FinFun n n') (f : FinFun k k') :
      (S.rename g).crename f = (S.crename f).rename g := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E =>
        simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f,
          proof_EType_rename_crename_comm E g.ext f]
      | tforall S E =>
        simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f,
          proof_EType_rename_crename_comm E g f]
      | cforall B E =>
        simp only [SType.rename, SType.crename, proof_CBound_rename_crename_comm,
          proof_EType_rename_crename_comm E g f.ext]
      | box T => simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f]
      | label S => simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f],
    proof_CType_rename_crename_comm {n m k n' k' : ℕ}
      (C : CType n m k) (g : FinFun n n') (f : FinFun k k') :
      (C.rename g).crename f = (C.crename f).rename g := by
      cases C with
      | capt C S =>
        simp only [CType.rename, CType.crename,
          CaptureSet.rename_crename_comm, proof_SType_rename_crename_comm S g f],
    proof_EType_rename_crename_comm {n m k n' k' : ℕ}
      (E : EType n m k) (g : FinFun n n') (f : FinFun k k') :
      (E.rename g).crename f = (E.crename f).rename g := by
      cases E with
      | ex T => simpa [EType.rename, EType.crename] using
          congrArg EType.ex (proof_CType_rename_crename_comm T g f.ext)
      | type T => simpa [EType.rename, EType.crename] using
          congrArg EType.type (proof_CType_rename_crename_comm T g f)
    apply proof_EType_rename_crename_comm

/-- `rename` and `crename` commute for `CType`. -/
theorem CType.rename_crename_comm {n m k n' k' : ℕ}
  (C : CType n m k) (g : FinFun n n') (f : FinFun k k') :
  (C.rename g).crename f = (C.crename f).rename g := by
  set_option maxHeartbeats 0 in
    have proof_CBound_rename_crename_comm {k k' n n' : Nat} (B : CBound n k)
        (g : FinFun n n') (f : FinFun k k') :
        (B.rename g).crename f = (B.crename f).rename g := by
      cases B <;> simp [CBound.rename, CBound.crename, CaptureSet.rename_crename_comm]
    let rec proof_EType_rename_crename_comm {n m k n' k' : ℕ}
      (E : EType n m k) (g : FinFun n n') (f : FinFun k k') :
      (E.rename g).crename f = (E.crename f).rename g := by
      cases E with
      | ex T => simpa [EType.rename, EType.crename] using
          congrArg EType.ex (proof_CType_rename_crename_comm T g f.ext)
      | type T => simpa [EType.rename, EType.crename] using
          congrArg EType.type (proof_CType_rename_crename_comm T g f),
    proof_SType_rename_crename_comm {n m k n' k' : ℕ}
      (S : SType n m k) (g : FinFun n n') (f : FinFun k k') :
      (S.rename g).crename f = (S.crename f).rename g := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E =>
        simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f,
          proof_EType_rename_crename_comm E g.ext f]
      | tforall S E =>
        simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f,
          proof_EType_rename_crename_comm E g f]
      | cforall B E =>
        simp only [SType.rename, SType.crename, proof_CBound_rename_crename_comm,
          proof_EType_rename_crename_comm E g f.ext]
      | box T => simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f]
      | label S => simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f],
    proof_CType_rename_crename_comm {n m k n' k' : ℕ}
      (C : CType n m k) (g : FinFun n n') (f : FinFun k k') :
      (C.rename g).crename f = (C.crename f).rename g := by
      cases C with
      | capt C S =>
        simp only [CType.rename, CType.crename,
          CaptureSet.rename_crename_comm, proof_SType_rename_crename_comm S g f]
    apply proof_CType_rename_crename_comm

/-- `rename` and `crename` commute for `SType`. -/
theorem SType.rename_crename_comm {n m k n' k' : ℕ}
  (S : SType n m k) (g : FinFun n n') (f : FinFun k k') :
  (S.rename g).crename f = (S.crename f).rename g := by
  set_option maxHeartbeats 0 in
    have proof_CBound_rename_crename_comm {k k' n n' : Nat} (B : CBound n k)
        (g : FinFun n n') (f : FinFun k k') :
        (B.rename g).crename f = (B.crename f).rename g := by
      cases B <;> simp [CBound.rename, CBound.crename, CaptureSet.rename_crename_comm]
    let rec proof_CType_rename_crename_comm {n m k n' k' : ℕ}
      (C : CType n m k) (g : FinFun n n') (f : FinFun k k') :
      (C.rename g).crename f = (C.crename f).rename g := by
      cases C with
      | capt C S =>
        simp only [CType.rename, CType.crename,
          CaptureSet.rename_crename_comm, proof_SType_rename_crename_comm S g f],
    proof_EType_rename_crename_comm {n m k n' k' : ℕ}
      (E : EType n m k) (g : FinFun n n') (f : FinFun k k') :
      (E.rename g).crename f = (E.crename f).rename g := by
      cases E with
      | ex T => simpa [EType.rename, EType.crename] using
          congrArg EType.ex (proof_CType_rename_crename_comm T g f.ext)
      | type T => simpa [EType.rename, EType.crename] using
          congrArg EType.type (proof_CType_rename_crename_comm T g f),
    proof_SType_rename_crename_comm {n m k n' k' : ℕ}
      (S : SType n m k) (g : FinFun n n') (f : FinFun k k') :
      (S.rename g).crename f = (S.crename f).rename g := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E =>
        simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f,
          proof_EType_rename_crename_comm E g.ext f]
      | tforall S E =>
        simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f,
          proof_EType_rename_crename_comm E g f]
      | cforall B E =>
        simp only [SType.rename, SType.crename, proof_CBound_rename_crename_comm,
          proof_EType_rename_crename_comm E g f.ext]
      | box T => simp only [SType.rename, SType.crename, proof_CType_rename_crename_comm T g f]
      | label S => simp only [SType.rename, SType.crename, proof_SType_rename_crename_comm S g f]
    apply proof_SType_rename_crename_comm

/-- `open` and `crename` commute for `EType`. -/
theorem EType.open_crename_comm {n m k k' : ℕ}
  (E : EType (n+1) m k) (y : Fin n) (f : FinFun k k') :
  (E.open y).crename f = (E.crename f).open y := by
  set_option maxHeartbeats 0 in
    have proof_EType_open_crename_comm {n m k k' : ℕ}
      (E : EType (n+1) m k) (y : Fin n) (f : FinFun k k') :
      (E.open y).crename f = (E.crename f).open y := by
      exact EType.rename_crename_comm E (FinFun.open y) f
    apply proof_EType_open_crename_comm

/-! ## Комposition of `crename` with `FinFun.open`

Capture-variable renaming composes through `FinFun.open`:
`(E.crename (FinFun.open c)).crename f = (E.crename f.ext).crename (FinFun.open (f c))`.
This is a key lemma for the `copen` commutation proof.
-/
theorem EType.crename_comp_open {E : EType n m (k+1)} {c : Fin k} {f : FinFun k k'} :
    (E.crename (FinFun.open c)).crename f = (E.crename f.ext).crename (FinFun.open (f c)) := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g]
    have proof_EType_crename_comp_open {k k' m n : Nat} {E : EType n m (k+1)} {c : Fin k} {f : FinFun k k'} :
        (E.crename (FinFun.open c)).crename f = (E.crename f.ext).crename (FinFun.open (f c)) := by
      simp only [proof_EType_crename_crename, FinFun.open_comp]
    apply proof_EType_crename_comp_open

/-- `topen` and `crename` commute for `EType`. -/
theorem EType.topen_crename {E : EType n (m+1) k} {X : Fin m} {f : FinFun k k'} :
    (E.topen X).crename f = (E.crename f).topen X := by
  set_option maxHeartbeats 0 in
    let rec proof_SType_trename_crename_comm {k k' m m' n : Nat} (S : SType n m k) (f : FinFun m m') (g : FinFun k k') :
      (S.trename f).crename g = (S.crename g).trename f := by
      match S with
      | SType.top => dsimp [SType.trename, SType.crename]
      | SType.tvar _ => dsimp [SType.trename, SType.crename]
      | SType.forall E1 E2 =>
        dsimp [SType.trename, SType.crename]
        rw [proof_CType_trename_crename_comm E1 f g, proof_EType_trename_crename_comm E2 f g]
      | SType.tforall S' E =>
        dsimp [SType.trename, SType.crename]
        rw [proof_SType_trename_crename_comm S' f g, proof_EType_trename_crename_comm E f.ext g]
      | SType.cforall B E =>
        dsimp [SType.trename, SType.crename, CBound.crename]
        rw [proof_EType_trename_crename_comm E f g.ext]
      | SType.box T =>
        dsimp [SType.trename, SType.crename]
        rw [proof_CType_trename_crename_comm T f g]
      | SType.label S' =>
        dsimp [SType.trename, SType.crename]
        rw [proof_SType_trename_crename_comm S' f g],
    proof_CType_trename_crename_comm {k k' m m' n : Nat} (C : CType n m k) (f : FinFun m m') (g : FinFun k k') :
      (C.trename f).crename g = (C.crename g).trename f := by
      match C with
      | CType.capt Ct S =>
        dsimp [CType.trename, CType.crename]
        rw [proof_SType_trename_crename_comm S f g],
    proof_EType_trename_crename_comm {k k' m m' n : Nat} (E : EType n m k) (f : FinFun m m') (g : FinFun k k') :
      (E.trename f).crename g = (E.crename g).trename f := by
      match E with
      | EType.ex T =>
        dsimp [EType.trename, EType.crename]
        rw [proof_CType_trename_crename_comm T f g.ext]
      | EType.type T =>
        dsimp [EType.trename, EType.crename]
        rw [proof_CType_trename_crename_comm T f g]
    have proof_EType_topen_crename {k k' m n : Nat} {E : EType n (m+1) k} {X : Fin m} {f : FinFun k k'} :
        (E.topen X).crename f = (E.crename f).topen X := by
      exact proof_EType_trename_crename_comm E (FinFun.open X) f
    apply proof_EType_topen_crename

/-- `copen` and `crename` commute for `EType`. -/
theorem EType.copen_crename {E : EType n m (k+1)} {c : Fin k} {f : FinFun k k'} :
    (E.copen c).crename f = (E.crename f.ext).copen (f c) := by
  set_option maxHeartbeats 0 in
    have proof_EType_copen_crename {k k' m n : Nat} {E : EType n m (k+1)} {c : Fin k} {f : FinFun k k'} :
        (E.copen c).crename f = (E.crename f.ext).copen (f c) := by
      exact EType.crename_comp_open
    apply proof_EType_copen_crename

/-! ## Weakening/crename commutation core lemmas

These are "core" lemmas showing the key algebraic identity that
`(weaken → f.ext) = (f → weaken)` for the crename operation.
-/

/--
Core lemma: `(E.crename FinFun.weaken).crename f.ext = (E.crename f).crename FinFun.weaken`.
-/
theorem EType.crename_weaken_comm_core {E : EType n m k} {f : FinFun k k'} :
    (E.crename FinFun.weaken).crename f.ext = (E.crename f).crename FinFun.weaken := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g]
    have proof_EType_crename_weaken_comm_core {k k' m n : Nat} {E : EType n m k} {f : FinFun k k'} :
        (E.crename FinFun.weaken).crename f.ext = (E.crename f).crename FinFun.weaken := by
      simp only [proof_EType_crename_crename, FinFun.weaken_comp_crename]
    apply proof_EType_crename_weaken_comm_core

/--
Core lemma: `(C.crename FinFun.weaken).crename f.ext = (C.crename f).crename FinFun.weaken`
for `CaptureSet`.
-/
theorem CaptureSet.crename_weaken_comm_core {C : CaptureSet n k} {f : FinFun k k'} :
    (C.crename FinFun.weaken).crename f.ext = (C.crename f).crename FinFun.weaken := by
  set_option maxHeartbeats 0 in
    have proof_CaptureSet_crename_weaken_comm_core {k k' n : Nat} {C : CaptureSet n k} {f : FinFun k k'} :
        (C.crename FinFun.weaken).crename f.ext = (C.crename f).crename FinFun.weaken := by
      simp only [CaptureSet.crename_comp, FinFun.weaken_comp_crename]
    apply proof_CaptureSet_crename_weaken_comm_core

/--
Core lemma: `(S.crename FinFun.weaken).crename f.ext = (S.crename f).crename FinFun.weaken`
for `SType`.
-/
theorem SType.crename_weaken_comm_core {S : SType n m k} {f : FinFun k k'} :
    (S.crename FinFun.weaken).crename f.ext = (S.crename f).crename FinFun.weaken := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g]
    have proof_SType_crename_weaken_comm_core {k k' m n : Nat} {S : SType n m k} {f : FinFun k k'} :
        (S.crename FinFun.weaken).crename f.ext = (S.crename f).crename FinFun.weaken := by
      simp only [proof_SType_crename_crename, FinFun.weaken_comp_crename]
    apply proof_SType_crename_weaken_comm_core

/-! ## Weakening/crename commutation lemmas -/

/-- Capture-variable weakening commutes with capture-variable renaming for `EType`:
`E.cweaken.crename f.ext = (E.crename f).cweaken`. -/
theorem EType.cweaken_crename_comm {E : EType n m k} {f : FinFun k k'} :
    (E.cweaken).crename f.ext = (E.crename f).cweaken := by
  set_option maxHeartbeats 0 in
    have proof_EType_cweaken_crename_comm {k k' m n : Nat} {E : EType n m k} {f : FinFun k k'} :
        (E.cweaken).crename f.ext = (E.crename f).cweaken := by
      exact EType.crename_weaken_comm_core
    apply proof_EType_cweaken_crename_comm

/-- Capture-variable weakening commutes with capture-variable renaming for `CaptureSet`. -/
theorem CaptureSet.cweaken_crename_comm {C : CaptureSet n k} {f : FinFun k k'} :
    (C.cweaken).crename f.ext = (C.crename f).cweaken := by
  set_option maxHeartbeats 0 in
    have proof_CaptureSet_cweaken_crename_comm {k k' n : Nat} {C : CaptureSet n k} {f : FinFun k k'} :
        (C.cweaken).crename f.ext = (C.crename f).cweaken := by
      exact CaptureSet.crename_weaken_comm_core
    apply proof_CaptureSet_cweaken_crename_comm

/-- Capture-variable weakening commutes with capture-variable renaming for `SType`. -/
theorem SType.cweaken_crename_comm {S : SType n m k} {f : FinFun k k'} :
    (S.cweaken).crename f.ext = (S.crename f).cweaken := by
  set_option maxHeartbeats 0 in
    have proof_SType_cweaken_crename_comm {k k' m n : Nat} {S : SType n m k} {f : FinFun k k'} :
        (S.cweaken).crename f.ext = (S.crename f).cweaken := by
      exact SType.crename_weaken_comm_core
    apply proof_SType_cweaken_crename_comm

/-- Term-variable weakening commutes with capture-variable renaming for `EType`. -/
theorem EType.weaken_crename_comm {E : EType n m k} {f : FinFun k k'} :
    (E.weaken).crename f = (E.crename f).weaken := by
  set_option maxHeartbeats 0 in
    have proof_EType_weaken_crename_comm {k k' m n : Nat} {E : EType n m k} {f : FinFun k k'} :
        (E.weaken).crename f = (E.crename f).weaken := by
      exact EType.rename_crename_comm E FinFun.weaken f
    apply proof_EType_weaken_crename_comm

/-- Term-variable weakening commutes with capture-variable renaming for `CaptureSet`. -/
theorem CaptureSet.weaken_crename_comm {C : CaptureSet n k} {f : FinFun k k'} :
    (C.weaken).crename f = (C.crename f).weaken := by
  set_option maxHeartbeats 0 in
    have proof_CaptureSet_weaken_crename_comm {k k' n : Nat} {C : CaptureSet n k} {f : FinFun k k'} :
        (C.weaken).crename f = (C.crename f).weaken := by
      exact CaptureSet.rename_crename_comm
    apply proof_CaptureSet_weaken_crename_comm

/-- Term-variable weakening commutes with capture-variable renaming for `SType`. -/
theorem SType.weaken_crename_comm {S : SType n m k} {f : FinFun k k'} :
    (S.weaken).crename f = (S.crename f).weaken := by
  set_option maxHeartbeats 0 in
    have proof_SType_weaken_crename_comm {k k' m n : Nat} {S : SType n m k} {f : FinFun k k'} :
        (S.weaken).crename f = (S.crename f).weaken := by
      exact SType.rename_crename_comm S FinFun.weaken f
    apply proof_SType_weaken_crename_comm

/-- Type-variable weakening commutes with capture-variable renaming for `EType`. -/
theorem EType.tweaken_crename_comm {E : EType n m k} {f : FinFun k k'} :
    (E.tweaken).crename f = (E.crename f).tweaken := by
  set_option maxHeartbeats 0 in
    let rec proof_SType_trename_crename_comm {k k' m m' n : Nat} (S : SType n m k) (f : FinFun m m') (g : FinFun k k') :
      (S.trename f).crename g = (S.crename g).trename f := by
      match S with
      | SType.top => dsimp [SType.trename, SType.crename]
      | SType.tvar _ => dsimp [SType.trename, SType.crename]
      | SType.forall E1 E2 =>
        dsimp [SType.trename, SType.crename]
        rw [proof_CType_trename_crename_comm E1 f g, proof_EType_trename_crename_comm E2 f g]
      | SType.tforall S' E =>
        dsimp [SType.trename, SType.crename]
        rw [proof_SType_trename_crename_comm S' f g, proof_EType_trename_crename_comm E f.ext g]
      | SType.cforall B E =>
        dsimp [SType.trename, SType.crename, CBound.crename]
        rw [proof_EType_trename_crename_comm E f g.ext]
      | SType.box T =>
        dsimp [SType.trename, SType.crename]
        rw [proof_CType_trename_crename_comm T f g]
      | SType.label S' =>
        dsimp [SType.trename, SType.crename]
        rw [proof_SType_trename_crename_comm S' f g],
    proof_CType_trename_crename_comm {k k' m m' n : Nat} (C : CType n m k) (f : FinFun m m') (g : FinFun k k') :
      (C.trename f).crename g = (C.crename g).trename f := by
      match C with
      | CType.capt Ct S =>
        dsimp [CType.trename, CType.crename]
        rw [proof_SType_trename_crename_comm S f g],
    proof_EType_trename_crename_comm {k k' m m' n : Nat} (E : EType n m k) (f : FinFun m m') (g : FinFun k k') :
      (E.trename f).crename g = (E.crename g).trename f := by
      match E with
      | EType.ex T =>
        dsimp [EType.trename, EType.crename]
        rw [proof_CType_trename_crename_comm T f g.ext]
      | EType.type T =>
        dsimp [EType.trename, EType.crename]
        rw [proof_CType_trename_crename_comm T f g]
    have proof_EType_tweaken_crename_comm {k k' m n : Nat} {E : EType n m k} {f : FinFun k k'} :
        (E.tweaken).crename f = (E.crename f).tweaken := by
      exact proof_EType_trename_crename_comm E FinFun.weaken f
    apply proof_EType_tweaken_crename_comm

/-! ## Type-variable renaming composition laws (`trename_trename`)

`trename` (type-variable renaming) composes functorially:
`E.trename f |> trename g = E.trename (g ∘ f)`.
-/

mutual

/-- `trename` composes: `(E.trename f).trename g = E.trename (g ∘ f)`. -/
theorem EType.trename_trename (E : EType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (E.trename f).trename g = E.trename (g ∘ f) := by
  match E with
  | EType.ex T =>
    dsimp [EType.trename]
    rw [CType.trename_trename T f g]
  | EType.type T =>
    dsimp [EType.trename]
    rw [CType.trename_trename T f g]

/-- `trename` composes: `(C.trename f).trename g = C.trename (g ∘ f)`. -/
theorem CType.trename_trename (C : CType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (C.trename f).trename g = C.trename (g ∘ f) := by
  match C with
  | CType.capt Ct S =>
    dsimp [CType.trename]
    rw [SType.trename_trename S f g]

/-- `trename` composes: `(S.trename f).trename g = S.trename (g ∘ f)`. -/
theorem SType.trename_trename (S : SType n m k) (f : FinFun m m') (g : FinFun m' m'') :
  (S.trename f).trename g = S.trename (g ∘ f) := by
  match S with
  | SType.top => dsimp [SType.trename]
  | SType.tvar _ => dsimp [SType.trename]
  | SType.forall E1 E2 =>
    dsimp [SType.trename]
    rw [CType.trename_trename E1 f g, EType.trename_trename E2 f g]
  | SType.tforall S' E =>
    dsimp [SType.trename]
    rw [SType.trename_trename S' f g, EType.trename_trename E f.ext g.ext]
    rw [← FinFun.ext_comp_symm (f := g) (g := f)]
  | SType.cforall B E =>
    dsimp [SType.trename]
    rw [EType.trename_trename E f g]
  | SType.box T =>
    dsimp [SType.trename]
    rw [CType.trename_trename T f g]
  | SType.label S' =>
    dsimp [SType.trename]
    rw [SType.trename_trename S' f g]

end

/-! ## Constructor-level `trename_trename` induction-step lemmas

These lemmas provide the induction-step cases for the mutual `trename_trename`
theorems above. Each lemma shows that if the `trename_trename` property holds
for subexpressions, then it holds for the compound expression built with this
constructor. Useful for modular induction/recursion proofs on `SType`, `CType`,
and `EType`.
-/

/-- `trename_trename` induction step for `SType.top`. -/
theorem SType.top_trename_trename {n m m' m'' k} (f : FinFun m m') (g : FinFun m' m'') :
    ((SType.top : SType n m k).trename f).trename g =
      (SType.top : SType n m k).trename (g ∘ f) :=
  rfl

/-- `trename_trename` induction step for `SType.tvar`. -/
theorem SType.tvar_trename_trename {n m m' m'' k} (X : Fin m) (f : FinFun m m')
    (g : FinFun m' m'') :
    ((SType.tvar X : SType n m k).trename f).trename g =
      (SType.tvar X : SType n m k).trename (g ∘ f) := by
  simp [SType.trename, Function.comp]

/-- `trename_trename` induction step for `SType.forall`. -/
theorem SType.forall_trename_trename {n m m' m'' k} (E1 : CType n m k) (E2 : EType (n+1) m k)
    (f : FinFun m m') (g : FinFun m' m'')
    (hC : (E1.trename f).trename g = E1.trename (g ∘ f))
    (hE : (E2.trename f).trename g = E2.trename (g ∘ f)) :
    ((SType.forall E1 E2).trename f).trename g =
      (SType.forall E1 E2).trename (g ∘ f) := by
  simp [SType.trename, hC, hE]

/-- `trename_trename` induction step for `SType.tforall`. -/
theorem SType.tforall_trename_trename {n m m' m'' k} (S : SType n m k) (E : EType n (m+1) k)
    (f : FinFun m m') (g : FinFun m' m'')
    (hS : (S.trename f).trename g = S.trename (g ∘ f))
    (hE : (E.trename (FinFun.ext f)).trename (FinFun.ext g) =
      E.trename ((FinFun.ext g) ∘ (FinFun.ext f))) :
    ((SType.tforall S E).trename f).trename g =
      (SType.tforall S E).trename (g ∘ f) := by
  simp [SType.trename, hS, hE, FinFun.ext_comp_symm (f := g) (g := f)]

/-- `trename_trename` induction step for `SType.cforall`. -/
theorem SType.cforall_trename_trename {n m m' m'' k} (B : CBound n k) (E : EType n m (k+1))
    (f : FinFun m m') (g : FinFun m' m'')
    (hE : (E.trename f).trename g = E.trename (g ∘ f)) :
    ((SType.cforall B E).trename f).trename g =
      (SType.cforall B E).trename (g ∘ f) := by
  simp [SType.trename, hE]

/-- `trename_trename` induction step for `SType.box`. -/
theorem SType.box_trename_trename {n m m' m'' k} (T : CType n m k) (f : FinFun m m')
    (g : FinFun m' m'') (hT : (T.trename f).trename g = T.trename (g ∘ f)) :
    ((SType.box T).trename f).trename g = (SType.box T).trename (g ∘ f) := by
  simp [SType.trename, hT]

/-- `trename_trename` induction step for `SType.label`. -/
theorem SType.label_trename_trename {n m m' m'' k} (S : SType n m k) (f : FinFun m m')
    (g : FinFun m' m'') (hS : (S.trename f).trename g = S.trename (g ∘ f)) :
    ((SType.label S).trename f).trename g = (SType.label S).trename (g ∘ f) := by
  simp [SType.trename, hS]

/-- `trename_trename` induction step for `CType.capt`. -/
theorem CType.capt_trename_trename {n m m' m'' k} (C : CaptureSet n k) (S : SType n m k)
    (f : FinFun m m') (g : FinFun m' m'')
    (hS : (S.trename f).trename g = S.trename (g ∘ f)) :
    ((CType.capt C S).trename f).trename g = (CType.capt C S).trename (g ∘ f) := by
  simp [CType.trename, hS]

/-- `trename_trename` induction step for `EType.ex`. -/
theorem EType.ex_trename_trename {n m m' m'' k} (T : CType n m (k+1)) (f : FinFun m m')
    (g : FinFun m' m'') (hT : (T.trename f).trename g = T.trename (g ∘ f)) :
    ((EType.ex T).trename f).trename g = (EType.ex T).trename (g ∘ f) := by
  simp [EType.trename, hT]

/-- `trename_trename` induction step for `EType.type`. -/
theorem EType.type_trename_trename {n m m' m'' k} (T : CType n m k) (f : FinFun m m')
    (g : FinFun m' m'') (hT : (T.trename f).trename g = T.trename (g ∘ f)) :
    ((EType.type T).trename f).trename g = (EType.type T).trename (g ∘ f) := by
  simp [EType.trename, hT]

/-! ## Renaming composition laws (`rename_rename`)

`rename` (term-variable renaming) composes functorially:
`(E.rename f).rename g = E.rename (g ∘ f)`.
-/

/-- `rename` composes for `CBound`: `(B.rename f).rename g = B.rename (g ∘ f)`. -/
theorem CBound.rename_rename (B : CBound n k) (f : FinFun n n') (g : FinFun n' n'') :
    (B.rename f).rename g = B.rename (g ∘ f) := by
  cases B
  · simp [CBound.rename, CaptureSet.rename_rename]
  · rfl

mutual

/-- `rename` composes: `(E.rename f).rename g = E.rename (g ∘ f)`. -/
theorem EType.rename_rename (E : EType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (E.rename f).rename g = E.rename (g ∘ f) := by
  match E with
  | EType.ex T =>
    dsimp [EType.rename]
    rw [CType.rename_rename T f g]
  | EType.type T =>
    dsimp [EType.rename]
    rw [CType.rename_rename T f g]

/-- `rename` composes: `(C.rename f).rename g = C.rename (g ∘ f)`. -/
theorem CType.rename_rename (C : CType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (C.rename f).rename g = C.rename (g ∘ f) := by
  match C with
  | CType.capt Ct S =>
    dsimp [CType.rename]
    rw [CaptureSet.rename_rename Ct f g, SType.rename_rename S f g]

/-- `rename` composes: `(S.rename f).rename g = S.rename (g ∘ f)`. -/
theorem SType.rename_rename (S : SType n m k) (f : FinFun n n') (g : FinFun n' n'') :
  (S.rename f).rename g = S.rename (g ∘ f) := by
  match S with
  | SType.top => dsimp [SType.rename]
  | SType.tvar _ => dsimp [SType.rename]
  | SType.forall E1 E2 =>
    dsimp [SType.rename]
    rw [CType.rename_rename E1 f g, EType.rename_rename E2 f.ext g.ext]
    rw [FinFun.ext_comp_symm (f := g) (g := f)]
  | SType.tforall S' E =>
    dsimp [SType.rename]
    rw [SType.rename_rename S' f g, EType.rename_rename E f g]
  | SType.cforall B E =>
    simp [SType.rename, CBound.rename_rename B f g, EType.rename_rename E f g]
  | SType.box T =>
    dsimp [SType.rename]
    rw [CType.rename_rename T f g]
  | SType.label S' =>
    dsimp [SType.rename]
    rw [SType.rename_rename S' f g]

end

/-! ## Commuting lemmas: `trename` vs `rename`

`trename` (term-variable renaming on types) commutes with `rename`:
`(E.rename g).trename f = (E.trename f).rename g`.
-/

mutual

/-- `trename` commutes with `rename` on `EType`. -/
theorem EType.trename_rename_comm (E : EType n m k) (g : FinFun n n') (f : FinFun m m') :
  (E.rename g).trename f = (E.trename f).rename g := by
  match E with
  | EType.ex T =>
    dsimp [EType.rename, EType.trename]
    rw [CType.trename_rename_comm T g f]
  | EType.type T =>
    dsimp [EType.rename, EType.trename]
    rw [CType.trename_rename_comm T g f]

/-- `trename` commutes with `rename` on `CType`. -/
theorem CType.trename_rename_comm (C : CType n m k) (g : FinFun n n') (f : FinFun m m') :
  (C.rename g).trename f = (C.trename f).rename g := by
  match C with
  | CType.capt Ct S =>
    dsimp [CType.rename, CType.trename]
    rw [SType.trename_rename_comm S g f]

/-- `trename` commutes with `rename` on `SType`. -/
theorem SType.trename_rename_comm (S : SType n m k) (g : FinFun n n') (f : FinFun m m') :
  (S.rename g).trename f = (S.trename f).rename g := by
  match S with
  | SType.top => dsimp [SType.rename, SType.trename]
  | SType.tvar _ => dsimp [SType.rename, SType.trename]
  | SType.forall E1 E2 =>
    dsimp [SType.rename, SType.trename]
    rw [CType.trename_rename_comm E1 g f, EType.trename_rename_comm E2 g.ext f]
  | SType.tforall S' E =>
    dsimp [SType.rename, SType.trename]
    rw [SType.trename_rename_comm S' g f, EType.trename_rename_comm E g f.ext]
  | SType.cforall B E =>
    dsimp [SType.rename, SType.trename, CBound.rename]
    rw [EType.trename_rename_comm E g f]
  | SType.box T =>
    dsimp [SType.rename, SType.trename]
    rw [CType.trename_rename_comm T g f]
  | SType.label S' =>
    dsimp [SType.rename, SType.trename]
    rw [SType.trename_rename_comm S' g f]

end

/-! ## Commuting lemmas: `trename` vs `crename`

`trename` (type-variable renaming) commutes with `crename` (capture-variable renaming):
`(E.trename f).crename g = (E.crename g).trename f`.
-/

mutual

/-- `trename` commutes with `crename` on `EType`. -/
theorem EType.trename_crename_comm (E : EType n m k) (f : FinFun m m') (g : FinFun k k') :
  (E.trename f).crename g = (E.crename g).trename f := by
  match E with
  | EType.ex T =>
    dsimp [EType.trename, EType.crename]
    rw [CType.trename_crename_comm T f g.ext]
  | EType.type T =>
    dsimp [EType.trename, EType.crename]
    rw [CType.trename_crename_comm T f g]

/-- `trename` commutes with `crename` on `CType`. -/
theorem CType.trename_crename_comm (C : CType n m k) (f : FinFun m m') (g : FinFun k k') :
  (C.trename f).crename g = (C.crename g).trename f := by
  match C with
  | CType.capt Ct S =>
    dsimp [CType.trename, CType.crename]
    rw [SType.trename_crename_comm S f g]

/-- `trename` commutes with `crename` on `SType`. -/
theorem SType.trename_crename_comm (S : SType n m k) (f : FinFun m m') (g : FinFun k k') :
  (S.trename f).crename g = (S.crename g).trename f := by
  match S with
  | SType.top => dsimp [SType.trename, SType.crename]
  | SType.tvar _ => dsimp [SType.trename, SType.crename]
  | SType.forall E1 E2 =>
    dsimp [SType.trename, SType.crename]
    rw [CType.trename_crename_comm E1 f g, EType.trename_crename_comm E2 f g]
  | SType.tforall S' E =>
    dsimp [SType.trename, SType.crename]
    rw [SType.trename_crename_comm S' f g, EType.trename_crename_comm E f.ext g]
  | SType.cforall B E =>
    dsimp [SType.trename, SType.crename, CBound.crename]
    rw [EType.trename_crename_comm E f g.ext]
  | SType.box T =>
    dsimp [SType.trename, SType.crename]
    rw [CType.trename_crename_comm T f g]
  | SType.label S' =>
    dsimp [SType.trename, SType.crename]
    rw [SType.trename_crename_comm S' f g]

end

/-! ## Derived corollaries: `trename` commutes with weakening/opening -/

/-- `trename` commutes with `open` for `EType`. -/
theorem EType.trename_open (E : EType (n+1) m k) (y : Fin n) (f : FinFun m m') :
  (E.open y).trename f = (E.trename f).open y := by
  dsimp [EType.open]
  exact EType.trename_rename_comm E (FinFun.open y) f

/-- `trename` commutes with `weaken` for `EType`. -/
theorem EType.trename_weaken (E : EType n m k) (f : FinFun m m') :
  (E.weaken).trename f = (E.trename f).weaken := by
  dsimp [EType.weaken]
  exact EType.trename_rename_comm E FinFun.weaken f

/-- `trename` commutes with `weaken` for `CType`. -/
theorem CType.trename_weaken (C : CType n m k) (f : FinFun m m') :
  (C.weaken).trename f = (C.trename f).weaken := by
  dsimp [CType.weaken]
  exact CType.trename_rename_comm C FinFun.weaken f

/-- `trename` commutes with `weaken` for `SType`. -/
theorem SType.trename_weaken (S : SType n m k) (f : FinFun m m') :
  (S.weaken).trename f = (S.trename f).weaken := by
  dsimp [SType.weaken]
  exact SType.trename_rename_comm S FinFun.weaken f

/-- `trename` commutes with `cweaken` for `EType`. -/
theorem EType.trename_cweaken (E : EType n m k) (f : FinFun m m') :
  (E.cweaken).trename f = (E.trename f).cweaken := by
  dsimp [EType.cweaken]
  rw [EType.trename_crename_comm E f FinFun.weaken]

/-- `trename` commutes with `cweaken` for `CType`. -/
theorem CType.trename_cweaken (C : CType n m k) (f : FinFun m m') :
  (C.cweaken).trename f = (C.trename f).cweaken := by
  dsimp [CType.cweaken]
  rw [CType.trename_crename_comm C f FinFun.weaken]

/-- `trename` commutes with `cweaken` for `SType`. -/
theorem SType.trename_cweaken (S : SType n m k) (f : FinFun m m') :
  (S.cweaken).trename f = (S.trename f).cweaken := by
  dsimp [SType.cweaken]
  rw [SType.trename_crename_comm S f FinFun.weaken]

/-- `trename` commutes with `cweaken1` for `EType`. -/
theorem EType.trename_cweaken1 (E : EType n m (k+1)) (f : FinFun m m') :
  (E.cweaken1).trename f = (E.trename f).cweaken1 := by
  dsimp [EType.cweaken1]
  rw [EType.trename_crename_comm E f FinFun.weaken.ext]

/-- `trename` commutes with `copen` for `EType`. -/
theorem EType.trename_copen (E : EType n m (k+1)) (c : Fin k) (f : FinFun m m') :
  (E.copen c).trename f = (E.trename f).copen c := by
  dsimp [EType.copen]
  rw [EType.trename_crename_comm E f (FinFun.open c)]

/-- `trename` commutes with `topen` for `EType`. -/
theorem EType.trename_topen (E : EType n (m+1) k) (X : Fin m) (f : FinFun m m') :
  (E.topen X).trename f = (E.trename f.ext).topen (f X) := by
  dsimp [EType.topen]
  rw [EType.trename_trename E (FinFun.open X) f]
  rw [FinFun.open_comp]
  rw [← EType.trename_trename E f.ext (FinFun.open (f X))]

/-- `trename` commutes with `tweaken` for `EType`. -/
theorem EType.trename_tweaken (E : EType n m k) (f : FinFun m m') :
  (E.tweaken).trename f.ext = (E.trename f).tweaken := by
  dsimp [EType.tweaken]
  rw [EType.trename_trename E FinFun.weaken f.ext]
  rw [FinFun.weaken_comp_crename (f := f)]
  rw [← EType.trename_trename E f FinFun.weaken]

/-! ## Combined weaken/cweaken commutation -/

/-- `trename` commutes with `cweaken.weaken` for `EType`. -/
theorem EType.trename_cweaken_weaken (E : EType n m k) (f : FinFun m m') :
  (E.cweaken.weaken).trename f = (E.trename f).cweaken.weaken := by
  dsimp [EType.weaken, EType.cweaken]
  rw [EType.trename_crename_comm E f FinFun.weaken]
  rw [EType.trename_rename_comm (E.crename FinFun.weaken) FinFun.weaken f]

/-- `trename` commutes with `cweaken.weaken` for `CType`. -/
theorem CType.trename_cweaken_weaken (C : CType n m k) (f : FinFun m m') :
  (C.cweaken.weaken).trename f = (C.trename f).cweaken.weaken := by
  dsimp [CType.weaken, CType.cweaken]
  rw [CType.trename_crename_comm C f FinFun.weaken]
  rw [CType.trename_rename_comm (C.crename FinFun.weaken) FinFun.weaken f]

/-- `trename` commutes with `cweaken.weaken` for `SType`. -/
theorem SType.trename_cweaken_weaken (S : SType n m k) (f : FinFun m m') :
  (S.cweaken.weaken).trename f = (S.trename f).cweaken.weaken := by
  dsimp [SType.weaken, SType.cweaken]
  rw [SType.trename_crename_comm S f FinFun.weaken]
  rw [SType.trename_rename_comm (S.crename FinFun.weaken) FinFun.weaken f]

/-! ## TBinding Renaming Commutation Lemmas

Commutation lemmas showing that `rename`, `trename`, `crename` operations on
`TBinding` commute with each other, or that weakening operations commute
with type-variable renaming.
-/

/-- `rename` and `trename` commute on `TBinding`. -/
theorem TBinding.rename_trename_comm {b : TBinding n m k} (r : FinFun n n') (t : FinFun m m') :
    (b.trename t).rename r = (b.rename r).trename t := by
  cases b
  case bound S =>
    simp [TBinding.trename, TBinding.rename]
    rw [SType.trename_rename_comm S r t]
  case inst S =>
    simp [TBinding.trename, TBinding.rename]
    rw [SType.trename_rename_comm S r t]

/-- `cweaken` (capture-variable weakening) commutes with `trename` on `TBinding`. -/
theorem TBinding.cweaken_trename_comm {b : TBinding n m k} (t : FinFun m m') :
    (b.trename t).cweaken = (b.cweaken).trename t := by
  cases b
  case bound S =>
    simp [TBinding.trename, TBinding.cweaken, TBinding.crename]
    rw [SType.trename_crename_comm S t FinFun.weaken]
  case inst S =>
    simp [TBinding.trename, TBinding.cweaken, TBinding.crename]
    rw [SType.trename_crename_comm S t FinFun.weaken]

/-- `weaken` (term-variable weakening) commutes with `trename` on `TBinding`. -/
theorem TBinding.weaken_trename_eq {b : TBinding n m k} (f : FinFun m m') :
    (b.trename f).weaken = (b.weaken).trename f :=
  TBinding.rename_trename_comm (b := b) FinFun.weaken f

/-! ## `rename`/`crename` with `FinFun.weaken.ext` then `FinFun.open 0` = identity

These lemmas state a fundamental algebraic identity: composing `rename FinFun.weaken.ext`
(the "extended weakening" which pushes a new variable at position 0) with
`rename (FinFun.open 0)` (which maps the new variable 0 back out) returns
the original term/type/capture set. The same holds for `crename`.

These are essential for proving properties of substitution and boundary typing.
-/

/-- `CaptureSet.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `CaptureSet`. -/
theorem CaptureSet.open_weaken_ext {C : CaptureSet (n+1) k} :
    (C.rename FinFun.weaken.ext).rename (FinFun.open 0) = C := by
  match C with
  | .empty => simp
  | .union C1 C2 =>
    simp [CaptureSet.rename, CaptureSet.open_weaken_ext (C := C1), CaptureSet.open_weaken_ext (C := C2)]
  | .singleton x =>
    cases x using Fin.cases <;> simp [FinFun.weaken, FinFun.ext, FinFun.open, CaptureSet.rename]
  | .csingleton c => simp

/-- `CBound.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `CBound`. -/
theorem CBound.open_weaken_ext {B : CBound (n+1) k} :
    (B.rename FinFun.weaken.ext).rename (FinFun.open 0) = B := by
  cases B <;> simp [CBound.rename, CaptureSet.open_weaken_ext]

/-- `Term.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `Term`. -/
theorem Term.open_weaken_ext {t : Term (n+1) m k} :
    (t.rename FinFun.weaken.ext).rename (FinFun.open 0) = t := by
  set_option maxHeartbeats 0 in
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_Term_rename_comp {k m n n' n'' : Nat} (t : Term n m k) (f : FinFun n n') (g : FinFun n' n'') :
        (t.rename f).rename g = t.rename (g ∘ f) := by
      induction t generalizing n' n'' <;>
        simp_all [Term.rename, CType.rename_rename, SType.rename_rename,
          CBound.rename_rename, CaptureSet.rename_rename, FinFun.ext_comp_symm]
    have proof_CaptureSet_rename_id {k n : Nat} (C : CaptureSet n k) : C.rename FinFun.id = C := by
      induction C <;> simp_all [CaptureSet.rename, FinFun.id]
    have proof_CBound_rename_id {k n : Nat} (B : CBound n k) : B.rename FinFun.id = B := by
      cases B <;> simp [CBound.rename, proof_CaptureSet_rename_id]
    let rec proof_EType_rename_id {k m n : Nat} (E : EType n m k) : E.rename FinFun.id = E := by
      match E with
      | .ex T => simp only [EType.rename, proof_CType_rename_id T]
      | .type T => simp only [EType.rename, proof_CType_rename_id T],
    proof_SType_rename_id {k m n : Nat} (S : SType n m k) : S.rename FinFun.id = S := by
      match S with
      | .top => rfl
      | .tvar X => rfl
      | .forall T E => simp only [SType.rename, FinFun.id_ext, proof_CType_rename_id T, proof_EType_rename_id E]
      | .tforall S E => simp only [SType.rename, proof_SType_rename_id S, proof_EType_rename_id E]
      | .cforall B E => simp only [SType.rename, proof_CBound_rename_id, proof_EType_rename_id E]
      | .box T => simp only [SType.rename, proof_CType_rename_id T]
      | .label S => simp only [SType.rename, proof_SType_rename_id S],
    proof_CType_rename_id {k m n : Nat} (C : CType n m k) : C.rename FinFun.id = C := by
      match C with
      | .capt C S => simp only [CType.rename, proof_CaptureSet_rename_id, proof_SType_rename_id S]
    have proof_Term_rename_id {k m n : Nat} (t : Term n m k) : t.rename FinFun.id = t := by
      induction t <;> simp_all [Term.rename, proof_CType_rename_id, proof_SType_rename_id,
        proof_CBound_rename_id, proof_CaptureSet_rename_id, FinFun.id_ext, FinFun.id]
    have proof_Term_open_weaken_ext {k m n : Nat} {t : Term (n+1) m k} :
        (t.rename FinFun.weaken.ext).rename (FinFun.open 0) = t := by
      rw [proof_Term_rename_comp, proof_open_weaken_ext_id, proof_Term_rename_id]
    apply proof_Term_open_weaken_ext

/-- `EType.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `EType`. -/
theorem EType.open_weaken_ext {E : EType (n+1) m k} :
    (E.rename FinFun.weaken.ext).rename (FinFun.open 0) = E := by
  set_option maxHeartbeats 0 in
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_CaptureSet_rename_id {k n : Nat} (C : CaptureSet n k) : C.rename FinFun.id = C := by
      induction C <;> simp_all [CaptureSet.rename, FinFun.id]
    have proof_CBound_rename_id {k n : Nat} (B : CBound n k) : B.rename FinFun.id = B := by
      cases B <;> simp [CBound.rename, proof_CaptureSet_rename_id]
    let rec proof_SType_rename_id {k m n : Nat} (S : SType n m k) : S.rename FinFun.id = S := by
      match S with
      | .top => rfl
      | .tvar X => rfl
      | .forall T E => simp only [SType.rename, FinFun.id_ext, proof_CType_rename_id T, proof_EType_rename_id E]
      | .tforall S E => simp only [SType.rename, proof_SType_rename_id S, proof_EType_rename_id E]
      | .cforall B E => simp only [SType.rename, proof_CBound_rename_id, proof_EType_rename_id E]
      | .box T => simp only [SType.rename, proof_CType_rename_id T]
      | .label S => simp only [SType.rename, proof_SType_rename_id S],
    proof_CType_rename_id {k m n : Nat} (C : CType n m k) : C.rename FinFun.id = C := by
      match C with
      | .capt C S => simp only [CType.rename, proof_CaptureSet_rename_id, proof_SType_rename_id S],
    proof_EType_rename_id {k m n : Nat} (E : EType n m k) : E.rename FinFun.id = E := by
      match E with
      | .ex T => simp only [EType.rename, proof_CType_rename_id T]
      | .type T => simp only [EType.rename, proof_CType_rename_id T]
    have proof_EType_open_weaken_ext {k m n : Nat} {E : EType (n+1) m k} :
        (E.rename FinFun.weaken.ext).rename (FinFun.open 0) = E := by
      rw [EType.rename_rename, proof_open_weaken_ext_id, proof_EType_rename_id]
    apply proof_EType_open_weaken_ext

/-- `CType.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `CType`. -/
theorem CType.open_weaken_ext {T : CType (n+1) m k} :
    (T.rename FinFun.weaken.ext).rename (FinFun.open 0) = T := by
  set_option maxHeartbeats 0 in
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_CaptureSet_rename_id {k n : Nat} (C : CaptureSet n k) : C.rename FinFun.id = C := by
      induction C <;> simp_all [CaptureSet.rename, FinFun.id]
    have proof_CBound_rename_id {k n : Nat} (B : CBound n k) : B.rename FinFun.id = B := by
      cases B <;> simp [CBound.rename, proof_CaptureSet_rename_id]
    let rec proof_EType_rename_id {k m n : Nat} (E : EType n m k) : E.rename FinFun.id = E := by
      match E with
      | .ex T => simp only [EType.rename, proof_CType_rename_id T]
      | .type T => simp only [EType.rename, proof_CType_rename_id T],
    proof_SType_rename_id {k m n : Nat} (S : SType n m k) : S.rename FinFun.id = S := by
      match S with
      | .top => rfl
      | .tvar X => rfl
      | .forall T E => simp only [SType.rename, FinFun.id_ext, proof_CType_rename_id T, proof_EType_rename_id E]
      | .tforall S E => simp only [SType.rename, proof_SType_rename_id S, proof_EType_rename_id E]
      | .cforall B E => simp only [SType.rename, proof_CBound_rename_id, proof_EType_rename_id E]
      | .box T => simp only [SType.rename, proof_CType_rename_id T]
      | .label S => simp only [SType.rename, proof_SType_rename_id S],
    proof_CType_rename_id {k m n : Nat} (C : CType n m k) : C.rename FinFun.id = C := by
      match C with
      | .capt C S => simp only [CType.rename, proof_CaptureSet_rename_id, proof_SType_rename_id S]
    have proof_CType_open_weaken_ext {k m n : Nat} {T : CType (n+1) m k} :
        (T.rename FinFun.weaken.ext).rename (FinFun.open 0) = T := by
      rw [CType.rename_rename, proof_open_weaken_ext_id, proof_CType_rename_id]
    apply proof_CType_open_weaken_ext

/-- `SType.open_weaken_ext`: `rename f.ext` then `rename (open 0)` is identity for `SType`. -/
theorem SType.open_weaken_ext {S : SType (n+1) m k} :
    (S.rename FinFun.weaken.ext).rename (FinFun.open 0) = S := by
  set_option maxHeartbeats 0 in
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_CaptureSet_rename_id {k n : Nat} (C : CaptureSet n k) : C.rename FinFun.id = C := by
      induction C <;> simp_all [CaptureSet.rename, FinFun.id]
    have proof_CBound_rename_id {k n : Nat} (B : CBound n k) : B.rename FinFun.id = B := by
      cases B <;> simp [CBound.rename, proof_CaptureSet_rename_id]
    let rec proof_CType_rename_id {k m n : Nat} (C : CType n m k) : C.rename FinFun.id = C := by
      match C with
      | .capt C S => simp only [CType.rename, proof_CaptureSet_rename_id, proof_SType_rename_id S],
    proof_EType_rename_id {k m n : Nat} (E : EType n m k) : E.rename FinFun.id = E := by
      match E with
      | .ex T => simp only [EType.rename, proof_CType_rename_id T]
      | .type T => simp only [EType.rename, proof_CType_rename_id T],
    proof_SType_rename_id {k m n : Nat} (S : SType n m k) : S.rename FinFun.id = S := by
      match S with
      | .top => rfl
      | .tvar X => rfl
      | .forall T E => simp only [SType.rename, FinFun.id_ext, proof_CType_rename_id T, proof_EType_rename_id E]
      | .tforall S E => simp only [SType.rename, proof_SType_rename_id S, proof_EType_rename_id E]
      | .cforall B E => simp only [SType.rename, proof_CBound_rename_id, proof_EType_rename_id E]
      | .box T => simp only [SType.rename, proof_CType_rename_id T]
      | .label S => simp only [SType.rename, proof_SType_rename_id S]
    have proof_SType_open_weaken_ext {k m n : Nat} {S : SType (n+1) m k} :
        (S.rename FinFun.weaken.ext).rename (FinFun.open 0) = S := by
      rw [SType.rename_rename, proof_open_weaken_ext_id, proof_SType_rename_id]
    apply proof_SType_open_weaken_ext

/-- `Term.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `Term`. -/
theorem Term.copen_cweaken_ext {t : Term n m (k+1)} :
    (t.crename FinFun.weaken.ext).crename (FinFun.open 0) = t := by
  set_option maxHeartbeats 0 in
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g]
    have proof_Term_crename_comp {k k' k'' m n : Nat} (t : Term n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (t.crename f).crename g = t.crename (g ∘ f) := by
      induction t generalizing k' k'' <;>
        simp_all [Term.crename, proof_CType_crename_crename, proof_SType_crename_crename,
          proof_CBound_crename_crename, CaptureSet.crename_comp, FinFun.ext_comp_symm]
    have proof_CBound_crename_id {k n : Nat} {b : CBound n k} : b.crename FinFun.id = b :=
      match b with
      | CBound.upper C => by simp [CBound.crename, CaptureSet.crename_id]
      | CBound.star => rfl
    let rec proof_EType_crename_id {k m n : Nat} {E : EType n m k} : E.crename FinFun.id = E :=
      match E with
      | EType.ex T => by
          simp [EType.crename, proof_CType_crename_id, FinFun.id_ext]
      | EType.type T => by
          simp [EType.crename, proof_CType_crename_id],
    proof_CType_crename_id {k m n : Nat} {C : CType n m k} : C.crename FinFun.id = C :=
      match C with
      | CType.capt C S => by
          simp [CType.crename, CaptureSet.crename_id, proof_SType_crename_id],
    proof_SType_crename_id {k m n : Nat} {S : SType n m k} : S.crename FinFun.id = S :=
      match S with
      | SType.top => rfl
      | SType.tvar X => rfl
      | SType.forall E1 E2 => by
          simp [SType.crename, proof_CType_crename_id, proof_EType_crename_id]
      | SType.tforall S E => by
          simp [SType.crename, proof_SType_crename_id, proof_EType_crename_id]
      | SType.cforall B E => by
          simp [SType.crename, proof_CBound_crename_id, proof_EType_crename_id, FinFun.id_ext]
      | SType.box T => by
          simp [SType.crename, proof_CType_crename_id]
      | SType.label S => by
          simp [SType.crename, proof_SType_crename_id]
    have proof_Term_crename_id {k m n : Nat} (t : Term n m k) : t.crename FinFun.id = t := by
      induction t <;> simp_all [Term.crename, proof_CType_crename_id, proof_SType_crename_id,
        proof_CBound_crename_id, CaptureSet.crename_id, FinFun.id_ext, FinFun.id]
    have proof_Term_copen_cweaken_ext {k m n : Nat} {t : Term n m (k+1)} :
        (t.crename FinFun.weaken.ext).crename (FinFun.open 0) = t := by
      rw [proof_Term_crename_comp, proof_open_weaken_ext_id, proof_Term_crename_id]
    apply proof_Term_copen_cweaken_ext

/-- `EType.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `EType`. -/
theorem EType.copen_cweaken_ext {E : EType n m (k+1)} :
    (E.crename FinFun.weaken.ext).crename (FinFun.open 0) = E := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g]
    have proof_CBound_crename_id {k n : Nat} {b : CBound n k} : b.crename FinFun.id = b :=
      match b with
      | CBound.upper C => by simp [CBound.crename, CaptureSet.crename_id]
      | CBound.star => rfl
    let rec proof_SType_crename_id {k m n : Nat} {S : SType n m k} : S.crename FinFun.id = S :=
      match S with
      | SType.top => rfl
      | SType.tvar X => rfl
      | SType.forall E1 E2 => by
          simp [SType.crename, proof_CType_crename_id, proof_EType_crename_id]
      | SType.tforall S E => by
          simp [SType.crename, proof_SType_crename_id, proof_EType_crename_id]
      | SType.cforall B E => by
          simp [SType.crename, proof_CBound_crename_id, proof_EType_crename_id, FinFun.id_ext]
      | SType.box T => by
          simp [SType.crename, proof_CType_crename_id]
      | SType.label S => by
          simp [SType.crename, proof_SType_crename_id],
    proof_CType_crename_id {k m n : Nat} {C : CType n m k} : C.crename FinFun.id = C :=
      match C with
      | CType.capt C S => by
          simp [CType.crename, CaptureSet.crename_id, proof_SType_crename_id],
    proof_EType_crename_id {k m n : Nat} {E : EType n m k} : E.crename FinFun.id = E :=
      match E with
      | EType.ex T => by
          simp [EType.crename, proof_CType_crename_id, FinFun.id_ext]
      | EType.type T => by
          simp [EType.crename, proof_CType_crename_id]
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_EType_copen_cweaken_ext {k m n : Nat} {E : EType n m (k+1)} :
        (E.crename FinFun.weaken.ext).crename (FinFun.open 0) = E := by
      rw [proof_EType_crename_crename, proof_open_weaken_ext_id, proof_EType_crename_id]
    apply proof_EType_copen_cweaken_ext

/-- `CType.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `CType`. -/
theorem CType.copen_cweaken_ext {T : CType n m (k+1)} :
    (T.crename FinFun.weaken.ext).crename (FinFun.open 0) = T := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g]
    have proof_CBound_crename_id {k n : Nat} {b : CBound n k} : b.crename FinFun.id = b :=
      match b with
      | CBound.upper C => by simp [CBound.crename, CaptureSet.crename_id]
      | CBound.star => rfl
    let rec proof_EType_crename_id {k m n : Nat} {E : EType n m k} : E.crename FinFun.id = E :=
      match E with
      | EType.ex T => by
          simp [EType.crename, proof_CType_crename_id, FinFun.id_ext]
      | EType.type T => by
          simp [EType.crename, proof_CType_crename_id],
    proof_SType_crename_id {k m n : Nat} {S : SType n m k} : S.crename FinFun.id = S :=
      match S with
      | SType.top => rfl
      | SType.tvar X => rfl
      | SType.forall E1 E2 => by
          simp [SType.crename, proof_CType_crename_id, proof_EType_crename_id]
      | SType.tforall S E => by
          simp [SType.crename, proof_SType_crename_id, proof_EType_crename_id]
      | SType.cforall B E => by
          simp [SType.crename, proof_CBound_crename_id, proof_EType_crename_id, FinFun.id_ext]
      | SType.box T => by
          simp [SType.crename, proof_CType_crename_id]
      | SType.label S => by
          simp [SType.crename, proof_SType_crename_id],
    proof_CType_crename_id {k m n : Nat} {C : CType n m k} : C.crename FinFun.id = C :=
      match C with
      | CType.capt C S => by
          simp [CType.crename, CaptureSet.crename_id, proof_SType_crename_id]
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_CType_copen_cweaken_ext {k m n : Nat} {T : CType n m (k+1)} :
        (T.crename FinFun.weaken.ext).crename (FinFun.open 0) = T := by
      rw [proof_CType_crename_crename, proof_open_weaken_ext_id, proof_CType_crename_id]
    apply proof_CType_copen_cweaken_ext

/-- `SType.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `SType`. -/
theorem SType.copen_cweaken_ext {S : SType n m (k+1)} :
    (S.crename FinFun.weaken.ext).crename (FinFun.open 0) = S := by
  set_option maxHeartbeats 0 in
    have proof_CBound_crename_crename {k k' k'' n : Nat} (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
        (b.crename f).crename g = b.crename (g ∘ f) := by
      cases b with
      | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
      | star => simp [CBound.crename]
    let rec proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, proof_CBound_crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g]
    have proof_CBound_crename_id {k n : Nat} {b : CBound n k} : b.crename FinFun.id = b :=
      match b with
      | CBound.upper C => by simp [CBound.crename, CaptureSet.crename_id]
      | CBound.star => rfl
    let rec proof_EType_crename_id {k m n : Nat} {E : EType n m k} : E.crename FinFun.id = E :=
      match E with
      | EType.ex T => by
          simp [EType.crename, proof_CType_crename_id, FinFun.id_ext]
      | EType.type T => by
          simp [EType.crename, proof_CType_crename_id],
    proof_CType_crename_id {k m n : Nat} {C : CType n m k} : C.crename FinFun.id = C :=
      match C with
      | CType.capt C S => by
          simp [CType.crename, CaptureSet.crename_id, proof_SType_crename_id],
    proof_SType_crename_id {k m n : Nat} {S : SType n m k} : S.crename FinFun.id = S :=
      match S with
      | SType.top => rfl
      | SType.tvar X => rfl
      | SType.forall E1 E2 => by
          simp [SType.crename, proof_CType_crename_id, proof_EType_crename_id]
      | SType.tforall S E => by
          simp [SType.crename, proof_SType_crename_id, proof_EType_crename_id]
      | SType.cforall B E => by
          simp [SType.crename, proof_CBound_crename_id, proof_EType_crename_id, FinFun.id_ext]
      | SType.box T => by
          simp [SType.crename, proof_CType_crename_id]
      | SType.label S => by
          simp [SType.crename, proof_SType_crename_id]
    have proof_open_weaken_ext_id {n : Nat} :
        (FinFun.open (0 : Fin (n+1))) ∘ FinFun.weaken.ext = FinFun.id := by
      funext i
      cases i using Fin.cases <;> rfl
    have proof_SType_copen_cweaken_ext {k m n : Nat} {S : SType n m (k+1)} :
        (S.crename FinFun.weaken.ext).crename (FinFun.open 0) = S := by
      rw [proof_SType_crename_crename, proof_open_weaken_ext_id, proof_SType_crename_id]
    apply proof_SType_copen_cweaken_ext

/-- `CaptureSet.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `CaptureSet`. -/
theorem CaptureSet.copen_cweaken_ext {C : CaptureSet n (k+1)} :
    (C.crename FinFun.weaken.ext).crename (FinFun.open 0) = C := by
  match C with
  | .empty => simp
  | .union C1 C2 =>
    simp [CaptureSet.crename, CaptureSet.copen_cweaken_ext (C := C1), CaptureSet.copen_cweaken_ext (C := C2)]
  | .singleton x => simp
  | .csingleton c =>
    cases c using Fin.cases <;> simp [FinFun.weaken, FinFun.ext, FinFun.open, CaptureSet.crename]

/-- `CBound.copen_cweaken_ext`: `crename f.ext` then `crename (open 0)` is identity for `CBound`. -/
theorem CBound.copen_cweaken_ext {B : CBound n (k+1)} :
    (B.crename FinFun.weaken.ext).crename (FinFun.open 0) = B := by
  cases B <;> simp [CBound.crename, CaptureSet.copen_cweaken_ext]

/-! ## Capture-variable renaming composition laws (`crename_crename`)

`crename` (capture-variable renaming) composes functorially:
`(T.crename f).crename g = T.crename (g ∘ f)` for all type-related structures.
-/

/-- `crename` composes: `(b.crename f).crename g = b.crename (g ∘ f)`. -/
theorem CBound.crename_crename (b : CBound n k) (f : FinFun k k') (g : FinFun k' k'') :
    (b.crename f).crename g = b.crename (g ∘ f) := by
  cases b with
  | upper C => simp [CBound.crename, CaptureSet.crename_comp C f g]
  | star => simp [CBound.crename]

mutual

/-- `crename` composes: `(E.crename f).crename g = E.crename (g ∘ f)`. -/
theorem EType.crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
    (E.crename f).crename g = E.crename (g ∘ f) := by
  set_option maxHeartbeats 0 in
    let rec proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, CBound.crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g]
    apply proof_EType_crename_crename

/-- `crename` composes: `(C.crename f).crename g = C.crename (g ∘ f)`. -/
theorem CType.crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
    (C.crename f).crename g = C.crename (g ∘ f) := by
  set_option maxHeartbeats 0 in
    let rec proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, CBound.crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g],
    proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g]
    apply proof_CType_crename_crename

/-- `crename` composes: `(S.crename f).crename g = S.crename (g ∘ f)`. -/
theorem SType.crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
    (S.crename f).crename g = S.crename (g ∘ f) := by
  set_option maxHeartbeats 0 in
    let rec proof_CType_crename_crename {n m k k' k'' : ℕ} (C : CType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (C.crename f).crename g = C.crename (g ∘ f) := by
      cases C with
      | capt C S => simp only [CType.crename, CaptureSet.crename_comp,
          proof_SType_crename_crename S f g],
    proof_EType_crename_crename {n m k k' k'' : ℕ} (E : EType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (E.crename f).crename g = E.crename (g ∘ f) := by
      cases E with
      | ex T => simp only [EType.crename, proof_CType_crename_crename T f.ext g.ext,
          FinFun.ext_comp_symm]
      | type T => simp only [EType.crename, proof_CType_crename_crename T f g],
    proof_SType_crename_crename {n m k k' k'' : ℕ} (S : SType n m k) (f : FinFun k k') (g : FinFun k' k'') :
        (S.crename f).crename g = S.crename (g ∘ f) := by
      cases S with
      | top => rfl
      | tvar X => rfl
      | «forall» T E => simp only [SType.crename, proof_CType_crename_crename T f g,
          proof_EType_crename_crename E f g]
      | tforall S E => simp only [SType.crename, proof_SType_crename_crename S f g,
          proof_EType_crename_crename E f g]
      | cforall B E => simp only [SType.crename, CBound.crename_crename,
          proof_EType_crename_crename E f.ext g.ext, FinFun.ext_comp_symm]
      | box T => simp only [SType.crename, proof_CType_crename_crename T f g]
      | label S => simp only [SType.crename, proof_SType_crename_crename S f g]
    apply proof_SType_crename_crename

end

/-!
# `crename` identity laws

Identity properties for the `crename` operation on all Capless types.
These mirror the corresponding `rename_id` and `trename_id` theorems.
-/

/-- Capture-variable renaming with the identity function is the identity on `CBound`. -/
theorem CBound.crename_id {b : CBound n k} : b.crename FinFun.id = b :=
  match b with
  | CBound.upper C => by simp [CBound.crename, CaptureSet.crename_id]
  | CBound.star => rfl

mutual

/-- Capture-variable renaming with the identity function is the identity on `SType`. -/
theorem SType.crename_id {S : SType n m k} : S.crename FinFun.id = S :=
  match S with
  | SType.top => rfl
  | SType.tvar X => rfl
  | SType.forall E1 E2 => by
      simp [SType.crename, CType.crename_id, EType.crename_id]
  | SType.tforall S E => by
      simp [SType.crename, SType.crename_id, EType.crename_id]
  | SType.cforall B E => by
      simp [SType.crename, CBound.crename_id, EType.crename_id, FinFun.id_ext]
  | SType.box T => by
      simp [SType.crename, CType.crename_id]
  | SType.label S => by
      simp [SType.crename, SType.crename_id]

/-- Capture-variable renaming with the identity function is the identity on `CType`. -/
theorem CType.crename_id {C : CType n m k} : C.crename FinFun.id = C :=
  match C with
  | CType.capt C S => by
      simp [CType.crename, CaptureSet.crename_id, SType.crename_id]

/-- Capture-variable renaming with the identity function is the identity on `EType`. -/
theorem EType.crename_id {E : EType n m k} : E.crename FinFun.id = E :=
  match E with
  | EType.ex T => by
      simp [EType.crename, CType.crename_id, FinFun.id_ext]
  | EType.type T => by
      simp [EType.crename, CType.crename_id]

end

/-!
# Reduction lemmas for `crename`

These lemmas provide the computational reduction rules for `crename` on each
constructor, making them available as named rewrite rules for reuse in proofs.
-/

lemma CBound.crename_upper (C : CaptureSet n k) (f : FinFun k k') :
    (CBound.upper C).crename f = CBound.upper (C.crename f) := by
  simp [CBound.crename]

lemma CBound.crename_star (f : FinFun k k') :
    (CBound.star (n:=n) (k:=k)).crename f = CBound.star := by
  simp [CBound.crename]

lemma CType.crename_capt (C : CaptureSet n k) (S : SType n m k) (f : FinFun k k') :
    (CType.capt C S).crename f = CType.capt (C.crename f) (S.crename f) := by
  simp [CType.crename]

lemma EType.crename_ex (T : CType n m (k+1)) (f : FinFun k k') :
    (EType.ex T).crename f = EType.ex (T.crename f.ext) := by
  simp [EType.crename]

lemma EType.crename_type (T : CType n m k) (f : FinFun k k') :
    (EType.type T).crename f = EType.type (T.crename f) := by
  simp [EType.crename]

lemma SType.crename_top (f : FinFun k k') :
    (SType.top (n:=n) (m:=m) (k:=k)).crename f = SType.top := by
  simp [SType.crename]

lemma SType.crename_tvar (X : Fin m) (f : FinFun k k') :
    (SType.tvar (n:=n) X).crename f = SType.tvar X := by
  simp [SType.crename]

lemma SType.crename_forall (E1 : CType n m k) (E2 : EType (n+1) m k) (f : FinFun k k') :
    (SType.forall E1 E2).crename f = SType.forall (E1.crename f) (E2.crename f) := by
  simp [SType.crename]

lemma SType.crename_tforall (S : SType n m k) (E : EType n (m+1) k) (f : FinFun k k') :
    (SType.tforall S E).crename f = SType.tforall (S.crename f) (E.crename f) := by
  simp [SType.crename]

lemma SType.crename_cforall (B : CBound n k) (E : EType n m (k+1)) (f : FinFun k k') :
    (SType.cforall B E).crename f = SType.cforall (B.crename f) (E.crename f.ext) := by
  simp [SType.crename]

lemma SType.crename_box (T : CType n m k) (f : FinFun k k') :
    (SType.box T).crename f = SType.box (T.crename f) := by
  simp [SType.crename]

lemma SType.crename_label (S : SType n m k) (f : FinFun k k') :
    (SType.label S).crename f = SType.label (S.crename f) := by
  simp [SType.crename]

end Capless
