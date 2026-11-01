import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! General list lemmas harvested from solved training problems. -/

open List

variable {α : Type*}

/-! ## Perm lemmas -/

lemma perm_symm_trans {l1 l2 l3 : List α} (h12 : l1.Perm l2) (h13 : l1.Perm l3) :
    l2.Perm l3 :=
  List.Perm.trans (List.Perm.symm h12) h13

lemma mem_of_mem_zip_tail {p : List α} {a b : α} (h : (a, b) ∈ p.zip p.tail) : a ∈ p ∧ b ∈ p := by
  rcases of_mem_zip h with ⟨ha, hb⟩
  exact ⟨ha, mem_of_mem_tail hb⟩

lemma getLast_eq_of_getLast?_eq_some {l : List α} {x : α} (h : l.getLast? = some x) (hne : l ≠ []) :
    l.getLast hne = x := by
  have hgl := getLast?_eq_some_getLast hne
  have : some (l.getLast hne) = some x := by rw [← hgl, h]
  exact Option.some_inj.mp this

lemma nodup_append_singleton_of_mem {l : List α} {x : α} (hx : x ∈ l) :
    ¬ (l ++ [x]).Nodup := by
  rw [nodup_append]
  intro ⟨_, _, hd⟩
  have hx' : x ∈ [x] := by simp
  exact hd x hx x hx' rfl

lemma nodup_append_singleton_of_not_mem {l : List α} {x : α} (hnd : l.Nodup) (hx : x ∉ l) :
    (l ++ [x]).Nodup := by
  rw [nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb
  have hb_eq_x : b = x := (mem_singleton.mp hb)
  rw [hb_eq_x]
  intro heq
  apply hx
  rw [← heq]
  exact ha

lemma exists_dup_of_not_nodup {l : List α} (h : ¬ l.Nodup) :
    ∃ (a : α) (l₁ l₂ l₃ : List α), l = l₁ ++ a :: l₂ ++ a :: l₃ := by
  induction l with
  | nil =>
    have hnil : Nodup ([] : List α) := by simp
    exact False.elim (h hnil)
  | cons x xs ih =>
    rw [nodup_cons] at h
    simp at h
    by_cases hm : x ∈ xs
    · rcases append_of_mem hm with ⟨s, t, hxs⟩
      refine ⟨x, [], s, t, ?_⟩
      simp [hxs]
    · have hxs := h hm
      rcases ih hxs with ⟨a, l₁, l₂, l₃, hxs'⟩
      refine ⟨a, x :: l₁, l₂, l₃, ?_⟩
      simp [hxs']

lemma zip_prefix_of_nonempty_append {A B : List α} (hA : A ≠ []) :
    (A.zip A.tail) <+: ((A ++ B).zip (A.tail ++ B)) := by
  induction A generalizing B with
  | nil => exact absurd rfl hA
  | cons a as ih =>
    simp
    cases as with
    | nil => simp
    | cons b bs =>
      simp
      apply ih
      simp

lemma zip_append_one (p : List α) (y : α) (hne : p ≠ []) :
    (p ++ [y]).zip ((p ++ [y]).tail) = p.zip p.tail ++ [(p.getLast hne, y)] := by
  induction p generalizing y with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil => simp
    | cons b bs =>
      have hne' : b :: bs ≠ [] := by simp
      have h_ih := ih y hne'
      simpa [getLast_cons] using h_ih

lemma zip_append_two (p : List α) (y z : α) (hne : p ≠ []) :
    (p ++ [y, z]).zip ((p ++ [y, z]).tail) =
    p.zip p.tail ++ [(p.getLast hne, y), (y, z)] := by
  induction p generalizing y z with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil => simp
    | cons b bs =>
      have hne' : b :: bs ≠ [] := by simp
      have h_ih := ih y z hne'
      simpa [getLast_cons] using h_ih

lemma split_at_last_occurrence {x : α} {l : List α} (h : x ∈ l) :
    ∃ (pre suf : List α), l = pre ++ [x] ++ suf ∧ x ∉ suf := by
  induction l generalizing x with
  | nil => simp at h
  | cons a as ih =>
    by_cases hx : x = a
    · rw [hx]
      by_cases hx' : a ∈ as
      · rcases ih hx' with ⟨pre, suf, heq, hxns⟩
        refine ⟨a :: pre, suf, ?_, hxns⟩
        simp [heq]
      · refine ⟨[], as, rfl, hx'⟩
    · have hmem : x ∈ as := by
        simpa [hx] using h
      rcases ih hmem with ⟨pre, suf, heq, hxns⟩
      refine ⟨a :: pre, suf, ?_, hxns⟩
      simp [heq]

/-! ## `List.ofFn` lemmas -/

/-- Split the flatten of `List.ofFn` for `Fin (k+1)` into the prefix (indices 0..k-1)
and the last element. This is useful for induction on `List.ofFn` via the push/snoc pattern. -/
lemma ofFn_flatten_snoc {α : Type} (k : ℕ) (f : Fin (k+1) → List α) :
    (List.ofFn f).flatten = (List.ofFn fun (i : Fin k) => f (Fin.castSucc i)).flatten ++
    f (Fin.last k) := by
  have h_add := List.ofFn_add (f := f) (n := k) (m := 1)
  have h_last : Fin.natAdd k 0 = (Fin.last k : Fin (k+1)) := by
    ext; simp
  calc
    (List.ofFn f).flatten
        = ((List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)) ++
            List.ofFn fun i : Fin 1 => f (Fin.natAdd k i)).flatten := by rw [h_add]
    _ = (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)).flatten ++
        (List.ofFn fun i : Fin 1 => f (Fin.natAdd k i)).flatten := by rw [List.flatten_append]
    _ = (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)).flatten ++
        f (Fin.natAdd k 0) := by simp
    _ = (List.ofFn fun i : Fin k => f (Fin.castLE (by omega) i)).flatten ++ f (Fin.last k) := by
      rw [h_last]
    _ = (List.ofFn fun i : Fin k => f (Fin.castSucc i)).flatten ++ f (Fin.last k) := by
      have h_cast : (fun (i : Fin k) => f (Fin.castLE (by omega : k ≤ k+1) i)) =
        (fun (i : Fin k) => f (Fin.castSucc i)) := by
        ext i
        have h : (Fin.castLE (by omega : k ≤ k+1) i : Fin (k+1)) = Fin.castSucc i := by
          ext; simp
        simp [h]
      rw [h_cast]

/-! ## `List.Forall₂` lemmas -/

lemma forall₂_append {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    {l₁' : List α} {l₂' : List β}
    (h : List.Forall₂ R l₁ l₂) (h' : List.Forall₂ R l₁' l₂') :
    List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := by
  induction h with
  | nil => exact h'
  | cons h htail ih =>
    apply List.Forall₂.cons h ih

lemma forall₂_get?_some {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {i : Nat}
    {a : α} (h : List.Forall₂ R l₁ l₂) (hget : l₁[i]? = some a) : ∃ b : β, l₂[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => cases hget
  | cons ha _ ih =>
    cases i with
    | zero =>
      simp at hget
      subst hget
      exact ⟨_, by simp, ha⟩
    | succ i =>
      simp at hget
      rcases ih hget with ⟨b, hb, hR⟩
      exact ⟨b, by simp [hb], hR⟩

/-- `Forall₂` is reflexive when the relation is pointwise reflexive. -/
lemma forall₂_refl_of_forall {α : Type*} {R : α → α → Prop} {l : List α}
    (h : ∀ a, R a a) : List.Forall₂ R l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x xs ih => exact List.Forall₂.cons (h x) ih

/-- If `R a b` implies `S (f a) (g b)` pointwise, then `Forall₂ R` lifts through `map`. -/
lemma forall₂_map {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ} {g : β → δ} {l₁ : List α} {l₂ : List β}
    (h : ∀ a b, R a b → S (f a) (g b)) (h₂ : List.Forall₂ R l₁ l₂) :
    List.Forall₂ S (List.map f l₁) (List.map g l₂) := by
  induction h₂ with
  | nil => exact List.Forall₂.nil
  | cons hd tl ih => exact List.Forall₂.cons (h _ _ hd) ih

/-- If `R (f x) (g x)` holds pointwise for all `x`, then `Forall₂ R` holds on the mapped lists. -/
lemma list_map_forall₂_of_pointwise {α β : Type*} {R : α → α → Prop}
    {f g : β → α} {l : List β} (h : ∀ x, R (f x) (g x)) :
    List.Forall₂ R (List.map f l) (List.map g l) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x xs ih => exact List.Forall₂.cons (h x) ih
