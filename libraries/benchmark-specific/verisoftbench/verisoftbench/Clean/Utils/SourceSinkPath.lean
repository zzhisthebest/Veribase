import Clean.Utils.SourceSinkPath
import verisoftbench.Common.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Theorems about `Run`, `Transition`, and `countTransitionInPath`, harvested from solved
    training problems. These are placed in `Utils.StateTransition` to match the repo. -/

namespace Utils.StateTransition

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma countTransitionInPath_zero_of_snd_not_mem (t : Transition S) (p : List S)
    (h : t.2 ∉ p) : countTransitionInPath t p = 0 := by
  dsimp [countTransitionInPath]
  apply List.count_eq_zero_of_not_mem
  intro hm
  rcases mem_of_mem_zip_tail hm with ⟨_, hb⟩
  exact h hb

lemma countTransitionInPath_zero_of_fst_not_mem (t : Transition S) (p : List S)
    (h : t.1 ∉ p) : countTransitionInPath t p = 0 := by
  dsimp [countTransitionInPath]
  apply List.count_eq_zero_of_not_mem
  intro hm
  rcases mem_of_mem_zip_tail hm with ⟨ha, _⟩
  exact h ha

lemma containsPath_append_fresh (R : Run S) (p : List S) (s y : S)
    (h_last : p.getLast? = some s) (h_contains : R.containsPath p)
    (h_notin : y ∉ p) (h_pos : R (s, y) > 0) : R.containsPath (p ++ [y]) := by
  have hne : p ≠ [] := by
    intro h; rw [h] at h_last; simp at h_last
  intro t
  dsimp [Run.containsPath, countTransitionInPath]
  have h_last_val : p.getLast hne = s := getLast_eq_of_getLast?_eq_some h_last hne
  have hzip_raw := zip_append_one p y hne
  have hzip : (p ++ [y]).zip ((p ++ [y]).tail) = p.zip p.tail ++ [(s, y)] := by
    simpa [h_last_val] using hzip_raw
  rw [hzip, List.count_append]
  by_cases ht : t = (s, y)
  · subst ht
    have hzero : List.count (s, y) (p.zip p.tail) = 0 :=
      countTransitionInPath_zero_of_snd_not_mem (s, y) p h_notin
    rw [hzero]
    simp
    exact Nat.one_le_of_lt h_pos
  · have : List.count t [(s, y)] = 0 := by
      rw [List.count_cons, List.count_nil]
      have hbeq : ((s, y) == t) = false := beq_false_of_ne (Ne.symm ht)
      simp [hbeq]
    rw [this, add_zero]
    exact h_contains t

lemma containsPath_of_containsPath_tail {R : Run S} {x : S} {xs : List S}
    (h : R.containsPath (x :: xs)) : R.containsPath xs := by
  intro t
  have hfull := h t
  dsimp [countTransitionInPath] at hfull ⊢
  cases xs with
  | nil => simp
  | cons y ys =>
    simp
    have h_suffix : ((y :: ys).zip ys) <:+ ((x, y) :: (y :: ys).zip ys) :=
      List.suffix_cons _ _
    have hcount := List.IsSuffix.count_le t h_suffix
    exact Nat.le_trans hcount hfull

lemma containsPath_of_prefix_dup (R : Run S) (x : S) (l₁ l₂ l₃ : List S)
    (h : R.containsPath (l₁ ++ x :: l₂ ++ x :: l₃)) :
    R.containsPath (x :: l₂ ++ [x]) := by
  induction l₁ generalizing R with
  | nil =>
    intro t
    have hfull := h t
    dsimp [countTransitionInPath] at hfull ⊢
    have h_nonempty : (x :: l₂ ++ [x]) ≠ [] := by simp
    have hprefix : ((x :: l₂ ++ [x]).zip (l₂ ++ [x])) <+:
        ((x :: l₂ ++ [x] ++ l₃).zip ((l₂ ++ [x]) ++ l₃)) :=
      zip_prefix_of_nonempty_append h_nonempty
    have h_simp_target : ((x :: l₂ ++ [x] ++ l₃).zip ((l₂ ++ [x]) ++ l₃)) =
        ((x :: l₂ ++ x :: l₃).zip (l₂ ++ x :: l₃)) := by simp
    rw [h_simp_target] at hprefix
    have hcount := List.IsPrefix.count_le t hprefix
    exact Nat.le_trans hcount hfull
  | cons hd tl ih =>
    have htail : R.containsPath (tl ++ x :: l₂ ++ x :: l₃) :=
      containsPath_of_containsPath_tail h
    exact ih R htail

lemma card_sdiff_toFinset_lt_of_append_singleton {p : List S} {y : S} (hy_notin : y ∉ p) :
    ((Finset.univ : Finset S) \ ((p ++ [y]).toFinset : Finset S)).card <
    ((Finset.univ : Finset S) \ p.toFinset).card := by
  have h_subset : ((Finset.univ : Finset S) \ ((p ++ [y]).toFinset : Finset S)) ⊂
      ((Finset.univ : Finset S) \ p.toFinset) := by
    constructor
    · intro x hx
      rcases Finset.mem_sdiff.1 hx with ⟨hx_univ, hx_notin⟩
      refine Finset.mem_sdiff.mpr ⟨hx_univ, ?_⟩
      intro hx_p
      apply hx_notin
      rw [List.mem_toFinset]
      rw [List.mem_append]
      left
      simpa using hx_p
    · intro h_rev
      have hy_in_univ : y ∈ (Finset.univ : Finset S) := Finset.mem_univ _
      have hy_notin_p : y ∉ p.toFinset := by simpa using hy_notin
      have hy_in_rhs : y ∈ ((Finset.univ : Finset S) \ p.toFinset) :=
        Finset.mem_sdiff.mpr ⟨hy_in_univ, hy_notin_p⟩
      have hy_notin_lhs : y ∉ ((Finset.univ : Finset S) \
          ((p ++ [y]).toFinset : Finset S)) := by
        intro h
        rcases Finset.mem_sdiff.1 h with ⟨_, hy_notin_p'⟩
        apply hy_notin_p'
        simp
      have hy_in_lhs := h_rev hy_in_rhs
      exact hy_notin_lhs hy_in_lhs
  exact Finset.card_lt_card h_subset

lemma acyclic_containsPath_nodup (R : Run S) (p : List S)
    (h_acyclic : R.isAcyclic) (h_contains : R.containsPath p) : p.Nodup := by
  by_contra! hnd
  rcases exists_dup_of_not_nodup hnd with ⟨x, l₁, l₂, l₃, hp⟩
  set cycle := x :: l₂ ++ [x] with hcycle_def
  have hcycle_len : cycle.length ≥ 2 := by
    dsimp [cycle]
    have hpos : 1 ≤ (l₂ ++ [x]).length := by simp
    calc
      (x :: l₂ ++ [x]).length = (l₂ ++ [x]).length + 1 := by simp
      _ ≥ 1 + 1 := Nat.add_le_add_right hpos 1
      _ = 2 := by norm_num
  have hcycle_head_last : cycle.head? = cycle.getLast? := by
    dsimp [cycle]
    have hhead : (x :: l₂ ++ [x]).head? = some x := by simp
    have hlast : (x :: l₂ ++ [x]).getLast? = some x := by
      have : (x :: l₂ ++ [x]) = (x :: l₂) ++ [x] := by simp
      rw [this, List.getLast?_append]
      simp
    calc
      (x :: l₂ ++ [x]).head? = some x := hhead
      _ = (x :: l₂ ++ [x]).getLast? := by rw [hlast]
  have h_contains_cycle : R.containsPath cycle := by
    have hp_contains : R.containsPath (l₁ ++ x :: l₂ ++ x :: l₃) := by
      simpa [hp] using h_contains
    have h := containsPath_of_prefix_dup R x l₁ l₂ l₃ hp_contains
    simpa [cycle] using h
  have h_hasCycle : R.hasCycle :=
    ⟨cycle, hcycle_len, hcycle_head_last, h_contains_cycle⟩
  exact h_acyclic h_hasCycle

lemma containsPath_append_two (R : Run S) (p : List S) (c y z : S)
    (h_last : p.getLast? = some c) (h_contains : R.containsPath p)
    (hy_notin : y ∉ p) (h_c_y_pos : R (c, y) > 0) (h_y_z_pos : R (y, z) > 0) :
    R.containsPath (p ++ [y, z]) := by
  have hne : p ≠ [] := by
    intro h; rw [h] at h_last; simp at h_last
  have h_last_val : p.getLast hne = c := getLast_eq_of_getLast?_eq_some h_last hne
  have h_c_mem_val : p.getLast hne ∈ p := List.getLast_mem hne
  have h_c_mem : c ∈ p := by rw [← h_last_val]; exact h_c_mem_val
  have h_c_ne_y : c ≠ y := by
    intro heq; subst heq; exact hy_notin h_c_mem
  have h_pair_ne : (c, y) ≠ (y, z) := by
    intro heq; apply h_c_ne_y; exact (Prod.mk.inj heq).1
  intro t
  dsimp [Run.containsPath, countTransitionInPath]
  have hzip_raw := zip_append_two p y z hne
  have hzip : (p ++ [y, z]).zip ((p ++ [y, z]).tail) =
      p.zip p.tail ++ [(c, y), (y, z)] := by
    simpa [h_last_val] using hzip_raw
  rw [hzip, List.count_append]
  have h_count_p : List.count t (p.zip p.tail) ≤ R t := by
    have h := h_contains t
    dsimp [Run.containsPath, countTransitionInPath] at h
    exact h
  have h0_cy : List.count (c, y) (p.zip p.tail) = 0 :=
    countTransitionInPath_zero_of_snd_not_mem (c, y) p hy_notin
  have h0_yz : List.count (y, z) (p.zip p.tail) = 0 :=
    countTransitionInPath_zero_of_fst_not_mem (y, z) p hy_notin
  by_cases ht1 : t = (c, y)
  · subst ht1
    rw [h0_cy]
    have hcount : List.count (c, y) [(c, y), (y, z)] = 1 := by
      rw [List.count_cons, List.count_cons, List.count_nil]
      have hbeq : ((y, z) == (c, y)) = false := beq_false_of_ne h_pair_ne.symm
      simp [hbeq]
    rw [hcount]
    exact Nat.one_le_of_lt h_c_y_pos
  · by_cases ht2 : t = (y, z)
    · subst ht2
      rw [h0_yz]
      have hcount : List.count (y, z) [(c, y), (y, z)] = 1 := by
        rw [List.count_cons, List.count_cons, List.count_nil]
        have hbeq : ((c, y) == (y, z)) = false := beq_false_of_ne h_pair_ne
        simp [hbeq]
      rw [hcount]
      exact Nat.one_le_of_lt h_y_z_pos
    · have hcount : List.count t [(c, y), (y, z)] = 0 := by
        rw [List.count_cons, List.count_cons, List.count_nil]
        have hbeq1 : ((c, y) == t) = false := beq_false_of_ne (Ne.symm ht1)
        have hbeq2 : ((y, z) == t) = false := beq_false_of_ne (Ne.symm ht2)
        simp [hbeq1, hbeq2]
      rw [hcount, add_zero]
      exact h_count_p

lemma countTransitionInPath_double (t : Transition S) (a b : S) :
    countTransitionInPath t [a, b] = (if t = (a, b) then 1 else 0) := by
  simp [countTransitionInPath, List.count_cons, List.count_nil]
  by_cases h : t = (a, b)
  · simp [h]
  · simp [h, Ne.symm h]

lemma countTransitionInPath_cons_cons (t : Transition S) (a b : S) (l : List S) :
    countTransitionInPath t (a :: b :: l) =
    (if t = (a, b) then 1 else 0) + countTransitionInPath t (b :: l) := by
  simp [countTransitionInPath, List.count_cons]
  by_cases h : t = (a, b)
  · simp [h, add_comm]
  · simp [h, Ne.symm h]

lemma countTransitionInPath_cons_le (t : Transition S) (a : S) (l : List S) :
    countTransitionInPath t l ≤ countTransitionInPath t (a :: l) := by
  cases l with
  | nil => simp [countTransitionInPath]
  | cons b bs =>
    rw [countTransitionInPath_cons_cons (a := a) (b := b) (l := bs)]
    omega

lemma countTransitionInPath_append_singleton_eq (t : Transition S) (l : List S) (x : S)
    (hne : l ≠ []) :
    countTransitionInPath t (l ++ [x]) = countTransitionInPath t l +
      (if t = (l.getLast hne, x) then 1 else 0) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a as ih0 =>
    cases as with
    | nil =>
      simp [countTransitionInPath]
      by_cases h : t = (a, x)
      · simp [h]
      · simp [h, Ne.symm h]
    | cons b bs =>
      have hne' : b :: bs ≠ [] := by simp
      have ih := ih0 hne'
      rw [List.cons_append] at ih
      rw [List.cons_append, List.cons_append]
      rw [countTransitionInPath_cons_cons (a := a) (b := b) (l := bs ++ [x]),
          countTransitionInPath_cons_cons (a := a) (b := b) (l := bs)]
      rw [ih]
      have hlast_eq : (b :: bs).getLast hne' = (a :: b :: bs).getLast hne := by simp
      simp only [hlast_eq, add_assoc]

lemma countTransitionInPath_suffix_le_append (t : Transition S) (pre suf : List S) (y : S) :
    countTransitionInPath t (y :: suf) ≤ countTransitionInPath t (pre ++ [y] ++ suf) := by
  induction pre with
  | nil => rfl
  | cons hd tl ih =>
    calc
      countTransitionInPath t (y :: suf) ≤ countTransitionInPath t (tl ++ [y] ++ suf) := ih
      _ ≤ countTransitionInPath t (hd :: (tl ++ [y] ++ suf)) :=
        countTransitionInPath_cons_le t hd _
      _ = countTransitionInPath t ((hd :: tl) ++ [y] ++ suf) := rfl

lemma countTransitionInPath_back_edge_not_mem_suffix (current y : S) (suf : List S)
    (hy_notin_suf : y ∉ suf) (h_ne : y ≠ current) :
    countTransitionInPath (current, y) (y :: suf) = 0 := by
  cases suf with
  | nil => simp [countTransitionInPath]
  | cons s ss =>
    rw [countTransitionInPath_cons_cons (a := y) (b := s) (l := ss)]
    have hpair_ne : (current, y) ≠ (y, s) := by
      intro heq
      have h_eq_pair := Prod.mk.inj heq
      rcases h_eq_pair with ⟨hc, hy'⟩
      apply h_ne; exact hc.symm
    simp [hpair_ne]
    apply countTransitionInPath_zero_of_snd_not_mem (current, y) (s :: ss)
    simpa using hy_notin_suf

lemma countTransitionInPath_cycle_non_closing (t : Transition S) (current y : S) (suf : List S)
    (h_suf_last : suf.getLast? = some current) (ht_ne : t ≠ (current, y)) :
    countTransitionInPath t (y :: (suf ++ [y])) = countTransitionInPath t (y :: suf) := by
  by_cases hsuf_empty : suf = []
  · subst hsuf_empty; simp at h_suf_last
  · have hne : y :: suf ≠ [] := by simp
    have hlast? : (y :: suf).getLast? = some current := by
      have : (y :: suf).getLast? = suf.getLast? := by
        cases suf with
        | nil => exact (hsuf_empty rfl).elim
        | cons s ss => simp
      rw [this]; exact h_suf_last
    have hlast : (y :: suf).getLast hne = current := by
      have hleq := List.getLast?_eq_some_getLast hne
      rw [hleq] at hlast?
      injection hlast?
    have h := countTransitionInPath_append_singleton_eq t (y :: suf) y hne
    simpa [hlast, ht_ne] using h

lemma countTransitionInPath_cycle_closing (current y : S) (suf : List S)
    (h_suf_last : suf.getLast? = some current) (h_ne : y ≠ current) (hy_notin_suf : y ∉ suf) :
    countTransitionInPath (current, y) (y :: (suf ++ [y])) = 1 := by
  by_cases hsuf_empty : suf = []
  · subst hsuf_empty; simp at h_suf_last
  · have hne' : y :: suf ≠ [] := by simp
    have hlast? : (y :: suf).getLast? = some current := by
      have : (y :: suf).getLast? = suf.getLast? := by
        cases suf with
        | nil => exact (hsuf_empty rfl).elim
        | cons s ss => simp
      rw [this]; exact h_suf_last
    have hlast : (y :: suf).getLast hne' = current :=
      getLast_eq_of_getLast?_eq_some hlast? hne'
    have hzero : countTransitionInPath (current, y) (y :: suf) = 0 :=
      countTransitionInPath_back_edge_not_mem_suffix current y suf hy_notin_suf h_ne
    have h := countTransitionInPath_append_singleton_eq (current, y) (y :: suf) y hne'
    simpa [hlast, hzero] using h

lemma acyclic_has_leaf_aux_1 (R : Run S) (root current : S)
    (path : List S)
    (h_acyclic : R.isAcyclic)
    (h_start : path.head? = some root)
    (h_end : path.getLast? = some current)
    (h_nonempty : path ≠ [])
    (h_contains : R.containsPath path)
    (h_has_out : ∃ y, y ∉ path ∧ R (current, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  have hasCycle_of_back_edge_in_path (R : Run S) (path : List S) (current y : S)
      (h_end : path.getLast? = some current)
      (h_contains : R.containsPath path)
      (h_y_in_path : y ∈ path)
      (h_edge : R (current, y) > 0) :
      R.hasCycle := by
    by_cases hy_eq_current : y = current
    · -- case y = current, cycle is just [current, current]
      rw [hy_eq_current] at h_edge
      refine ⟨[current, current], by simp, by simp, ?_⟩
      intro t
      rw [countTransitionInPath_double]
      split_ifs with ht
      · subst ht
        have : 0 < R (current, current) := h_edge
        omega
      · exact Nat.zero_le _
    · -- case y ≠ current, need to split path at the last occurrence of y
      have hsplit := split_at_last_occurrence h_y_in_path
      rcases hsplit with ⟨pre, suf, hpath_eq, hy_notin_suf⟩
      have h_suf_last : suf.getLast? = some current := by
        rw [hpath_eq] at h_end
        cases suf with
        | nil =>
          simp at h_end
          have hy_eq : y = current := by simpa using h_end
          exact absurd hy_eq hy_eq_current
        | cons s ss =>
          simpa [List.getLast?_append] using h_end
      set cycle := y :: (suf ++ [y]) with hcycle_def
      have h_cycle_len : cycle.length ≥ 2 := by
        dsimp [cycle]
        simp
      have h_cycle_head_last : cycle.head? = cycle.getLast? := by
        dsimp [cycle]
        have hlast : (y :: (suf ++ [y])).getLast? = some y := by
          calc
            (y :: (suf ++ [y])).getLast? = ((y :: suf) ++ [y]).getLast? := by simp
            _ = [y].getLast? := by
              rw [List.getLast?_append_of_ne_nil (y :: suf) (by simp)]
            _ = some y := by simp
        simpa using hlast.symm
      have h_cycle_contains : R.containsPath cycle := by
        intro t
        dsimp [cycle]
        have h_count_suf_le : countTransitionInPath t (y :: suf) ≤
            countTransitionInPath t (pre ++ [y] ++ suf) :=
          countTransitionInPath_suffix_le_append t pre suf y
        by_cases ht : t = (current, y)
        · subst ht
          have h_count_cycle : countTransitionInPath (current, y) (y :: (suf ++ [y])) = 1 :=
            countTransitionInPath_cycle_closing current y suf h_suf_last hy_eq_current hy_notin_suf
          rw [h_count_cycle]
          omega
        · have h_count_cycle : countTransitionInPath t (y :: (suf ++ [y])) =
              countTransitionInPath t (y :: suf) :=
            countTransitionInPath_cycle_non_closing t current y suf h_suf_last ht
          rw [h_count_cycle]
          calc
            countTransitionInPath t (y :: suf) ≤ countTransitionInPath t (pre ++ [y] ++ suf) :=
              h_count_suf_le
            _ ≤ R t := by rw [← hpath_eq]; exact h_contains t
      exact ⟨cycle, h_cycle_len, h_cycle_head_last, h_cycle_contains⟩
  let rec leaf_from_path (R : Run S) (root current : S)
      (path : List S) (h_acyclic : R.isAcyclic)
      (h_start : path.head? = some root) (h_end : path.getLast? = some current)
      (h_nonempty : path ≠ []) (h_contains : R.containsPath path) :
      ∃ leaf, R.isLeaf root leaf := by
    classical
    by_cases hout : ∀ y, R (current, y) = 0
    · exact ⟨current, ⟨⟨path, h_start, h_end, h_nonempty, h_contains⟩, hout⟩⟩
    · push_neg at hout
      obtain ⟨y, hy⟩ := hout
      have hpos : R (current, y) > 0 := Nat.pos_of_ne_zero hy
      have hfresh : y ∉ path := by
        intro hm
        exact h_acyclic (hasCycle_of_back_edge_in_path R path current y h_end h_contains hm hpos)
      apply leaf_from_path R root y (path ++ [y]) h_acyclic
      · cases path with
        | nil => exact (h_nonempty rfl).elim
        | cons a as => simpa using h_start
      · simp
      · simp
      · exact containsPath_append_fresh R path current y h_end h_contains hfresh hpos
  termination_by ((Finset.univ : Finset S) \ path.toFinset).card
  decreasing_by exact card_sdiff_toFinset_lt_of_append_singleton hfresh
  exact leaf_from_path R root current path h_acyclic h_start h_end h_nonempty h_contains

/-- In an acyclic run `R` where node `s` has net flow 1 and every node other than `s` and `d`
    has net flow 0, there exists a Nodup path from `s` to `d` that is contained in `R`. -/
lemma acyclic_exists_path_source_to_sink (R : Run S) (s d : S)
    (h_acyclic : R.isAcyclic)
    (h_source : R.netFlow s = 1)
    (h_others : ∀ x, x ≠ s → x ≠ d → R.netFlow x = 0) :
    ∃ (path : List S), path.head? = some s ∧ path.getLast? = some d ∧
      path ≠ [] ∧ R.containsPath path ∧ path.Nodup := by
  have hasCycle_of_back_edge_in_path (R : Run S) (path : List S) (current y : S)
      (h_end : path.getLast? = some current)
      (h_contains : R.containsPath path)
      (h_y_in_path : y ∈ path)
      (h_edge : R (current, y) > 0) :
      R.hasCycle := by
    by_cases hy_eq_current : y = current
    · -- case y = current, cycle is just [current, current]
      rw [hy_eq_current] at h_edge
      refine ⟨[current, current], by simp, by simp, ?_⟩
      intro t
      rw [countTransitionInPath_double]
      split_ifs with ht
      · subst ht
        have : 0 < R (current, current) := h_edge
        omega
      · exact Nat.zero_le _
    · -- case y ≠ current, need to split path at the last occurrence of y
      have hsplit := split_at_last_occurrence h_y_in_path
      rcases hsplit with ⟨pre, suf, hpath_eq, hy_notin_suf⟩
      have h_suf_last : suf.getLast? = some current := by
        rw [hpath_eq] at h_end
        cases suf with
        | nil =>
          simp at h_end
          have hy_eq : y = current := by simpa using h_end
          exact absurd hy_eq hy_eq_current
        | cons s ss =>
          simpa [List.getLast?_append] using h_end
      set cycle := y :: (suf ++ [y]) with hcycle_def
      have h_cycle_len : cycle.length ≥ 2 := by
        dsimp [cycle]
        simp
      have h_cycle_head_last : cycle.head? = cycle.getLast? := by
        dsimp [cycle]
        have hlast : (y :: (suf ++ [y])).getLast? = some y := by
          calc
            (y :: (suf ++ [y])).getLast? = ((y :: suf) ++ [y]).getLast? := by simp
            _ = [y].getLast? := by
              rw [List.getLast?_append_of_ne_nil (y :: suf) (by simp)]
            _ = some y := by simp
        simpa using hlast.symm
      have h_cycle_contains : R.containsPath cycle := by
        intro t
        dsimp [cycle]
        have h_count_suf_le : countTransitionInPath t (y :: suf) ≤
            countTransitionInPath t (pre ++ [y] ++ suf) :=
          countTransitionInPath_suffix_le_append t pre suf y
        by_cases ht : t = (current, y)
        · subst ht
          have h_count_cycle : countTransitionInPath (current, y) (y :: (suf ++ [y])) = 1 :=
            countTransitionInPath_cycle_closing current y suf h_suf_last hy_eq_current hy_notin_suf
          rw [h_count_cycle]
          omega
        · have h_count_cycle : countTransitionInPath t (y :: (suf ++ [y])) =
              countTransitionInPath t (y :: suf) :=
            countTransitionInPath_cycle_non_closing t current y suf h_suf_last ht
          rw [h_count_cycle]
          calc
            countTransitionInPath t (y :: suf) ≤ countTransitionInPath t (pre ++ [y] ++ suf) :=
              h_count_suf_le
            _ ≤ R t := by rw [← hpath_eq]; exact h_contains t
      exact ⟨cycle, h_cycle_len, h_cycle_head_last, h_cycle_contains⟩
  let rec leaf_from_path (R : Run S) (root current : S)
      (path : List S) (h_acyclic : R.isAcyclic)
      (h_start : path.head? = some root) (h_end : path.getLast? = some current)
      (h_nonempty : path ≠ []) (h_contains : R.containsPath path) :
      ∃ leaf, R.isLeaf root leaf := by
    classical
    by_cases hout : ∀ y, R (current, y) = 0
    · exact ⟨current, ⟨⟨path, h_start, h_end, h_nonempty, h_contains⟩, hout⟩⟩
    · push_neg at hout
      obtain ⟨y, hy⟩ := hout
      have hpos : R (current, y) > 0 := Nat.pos_of_ne_zero hy
      have hfresh : y ∉ path := by
        intro hm
        exact h_acyclic (hasCycle_of_back_edge_in_path R path current y h_end h_contains hm hpos)
      apply leaf_from_path R root y (path ++ [y]) h_acyclic
      · cases path with
        | nil => exact (h_nonempty rfl).elim
        | cons a as => simpa using h_start
      · simp
      · simp
      · exact containsPath_append_fresh R path current y h_end h_contains hfresh hpos
  termination_by ((Finset.univ : Finset S) \ path.toFinset).card
  decreasing_by exact card_sdiff_toFinset_lt_of_append_singleton hfresh
  classical
  have hs : R.containsPath [s] := by intro t; simp [countTransitionInPath]
  obtain ⟨leaf, ⟨⟨path, hstart, hend, hne, hpath⟩, hout⟩⟩ :=
    leaf_from_path R s s [s] h_acyclic (by simp) (by simp) (by simp) hs
  have hsum_nonneg : 0 ≤ ∑ y : S, (R (y, leaf) : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hflow : R.netFlow leaf = -(∑ y : S, (R (y, leaf) : ℤ)) := by
    simp [Run.netFlow, hout]
  have hls : leaf ≠ s := by
    intro heq
    rw [heq, h_source] at hflow
    rw [heq] at hsum_nonneg
    omega
  have hin : ∃ y, 0 < R (y, leaf) := by
    have aux : ∀ q : List S, q.length ≥ 2 → q.getLast? = some leaf →
        R.containsPath q → ∃ y, 0 < R (y, leaf) := by
      intro q
      induction q with
      | nil => simp
      | cons a as ih =>
        intro hlen hl hc
        cases as with
        | nil => simp at hlen
        | cons b bs =>
          cases bs with
          | nil =>
            have hb : b = leaf := by simpa using hl
            subst b
            refine ⟨a, ?_⟩
            have hh := hc (a, leaf)
            simp [countTransitionInPath] at hh
            omega
          | cons c cs =>
            exact ih (by simp) (by simpa using hl) (containsPath_of_containsPath_tail hc)
    apply aux path ?_ hend hpath
    cases path with
    | nil => exact (hne rfl).elim
    | cons a as =>
      cases as with
      | nil =>
        have ha : a = s := by simpa using hstart
        have hb : a = leaf := by simpa using hend
        exact (hls (hb.symm.trans ha)).elim
      | cons b bs => simp
  have hld : leaf = d := by
    by_contra hld
    have hz := h_others leaf hls hld
    have hsumzero : (∑ y : S, (R (y, leaf) : ℤ)) = 0 := by omega
    obtain ⟨y, hy⟩ := hin
    have hle : (R (y, leaf) : ℤ) ≤ ∑ z : S, (R (z, leaf) : ℤ) :=
      Finset.single_le_sum (fun z _ => Nat.cast_nonneg (R (z, leaf))) (Finset.mem_univ y)
    omega
  exact ⟨path, hstart, hld ▸ hend, hne, hpath, acyclic_containsPath_nodup R path h_acyclic hpath⟩

lemma hasCycle_of_back_edge_in_path (R : Run S) (path : List S) (current y : S)
    (h_end : path.getLast? = some current)
    (h_contains : R.containsPath path)
    (h_y_in_path : y ∈ path)
    (h_edge : R (current, y) > 0) :
    R.hasCycle := by
  by_cases hy_eq_current : y = current
  · -- case y = current, cycle is just [current, current]
    rw [hy_eq_current] at h_edge
    refine ⟨[current, current], by simp, by simp, ?_⟩
    intro t
    rw [countTransitionInPath_double]
    split_ifs with ht
    · subst ht
      have : 0 < R (current, current) := h_edge
      omega
    · exact Nat.zero_le _
  · -- case y ≠ current, need to split path at the last occurrence of y
    have hsplit := split_at_last_occurrence h_y_in_path
    rcases hsplit with ⟨pre, suf, hpath_eq, hy_notin_suf⟩
    have h_suf_last : suf.getLast? = some current := by
      rw [hpath_eq] at h_end
      cases suf with
      | nil =>
        simp at h_end
        have hy_eq : y = current := by simpa using h_end
        exact absurd hy_eq hy_eq_current
      | cons s ss =>
        simpa [List.getLast?_append] using h_end
    set cycle := y :: (suf ++ [y]) with hcycle_def
    have h_cycle_len : cycle.length ≥ 2 := by
      dsimp [cycle]
      simp
    have h_cycle_head_last : cycle.head? = cycle.getLast? := by
      dsimp [cycle]
      have hlast : (y :: (suf ++ [y])).getLast? = some y := by
        calc
          (y :: (suf ++ [y])).getLast? = ((y :: suf) ++ [y]).getLast? := by simp
          _ = [y].getLast? := by
            rw [List.getLast?_append_of_ne_nil (y :: suf) (by simp)]
          _ = some y := by simp
      simpa using hlast.symm
    have h_cycle_contains : R.containsPath cycle := by
      intro t
      dsimp [cycle]
      have h_count_suf_le : countTransitionInPath t (y :: suf) ≤
          countTransitionInPath t (pre ++ [y] ++ suf) :=
        countTransitionInPath_suffix_le_append t pre suf y
      by_cases ht : t = (current, y)
      · subst ht
        have h_count_cycle : countTransitionInPath (current, y) (y :: (suf ++ [y])) = 1 :=
          countTransitionInPath_cycle_closing current y suf h_suf_last hy_eq_current hy_notin_suf
        rw [h_count_cycle]
        omega
      · have h_count_cycle : countTransitionInPath t (y :: (suf ++ [y])) =
            countTransitionInPath t (y :: suf) :=
          countTransitionInPath_cycle_non_closing t current y suf h_suf_last ht
        rw [h_count_cycle]
        calc
          countTransitionInPath t (y :: suf) ≤ countTransitionInPath t (pre ++ [y] ++ suf) :=
            h_count_suf_le
          _ ≤ R t := by rw [← hpath_eq]; exact h_contains t
    exact ⟨cycle, h_cycle_len, h_cycle_head_last, h_cycle_contains⟩

/-! ### General Finset and List lemmas -/

lemma Finset.sum_nat_sub_eq_sub_sum {ι : Type*} [Fintype ι] (a b : ι → ℕ) (h : ∀ i, b i ≤ a i) :
    (∑ i : ι, ((a i - b i : ℕ) : ℤ)) = (∑ i : ι, (a i : ℤ)) - (∑ i : ι, (b i : ℤ)) := by
  calc
    (∑ i : ι, ((a i - b i : ℕ) : ℤ)) = (∑ i : ι, ((a i : ℤ) - (b i : ℤ))) := by
      refine Finset.sum_congr rfl (λ i _ => ?_)
      rw [Nat.cast_sub (h i)]
    _ = (∑ i : ι, (a i : ℤ)) - (∑ i : ι, (b i : ℤ)) := by rw [Finset.sum_sub_distrib]

theorem sum_count_by_snd {α : Type*} [DecidableEq α] [Fintype α] (L : List (α × S)) (x : S) :
    (∑ y : α, (List.count (y, x) L : ℤ)) = (List.countP (λ p : α × S => decide (p.2 = x)) L : ℤ) := by
  induction L with
  | nil => simp
  | cons p L' ih =>
    rcases p with ⟨a, b⟩
    by_cases hx : b = x
    · subst b
      simp only [List.count_cons, List.countP_cons, decide_true, Nat.cast_add, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ih]
    · have h_neq : decide (b = x) = false := by simp [hx]
      calc
        (∑ y : α, (List.count (y, x) ((a, b) :: L') : ℤ))
            = (∑ y : α, (List.count (y, x) L' : ℤ)) := by
          refine Finset.sum_congr rfl (λ y hy => ?_)
          simp [hx]
        _ = (List.countP (λ p : α × S => decide (p.2 = x)) L' : ℤ) := ih
        _ = (List.countP (λ p : α × S => decide (p.2 = x)) ((a, b) :: L') : ℤ) := by
          simp [h_neq]

theorem sum_count_by_fst {β : Type*} [DecidableEq β] [Fintype β] (L : List (S × β)) (x : S) :
    (∑ y : β, (List.count (x, y) L : ℤ)) = (List.countP (λ p : S × β => decide (p.1 = x)) L : ℤ) := by
  induction L with
  | nil => simp
  | cons p L' ih =>
    rcases p with ⟨a, b⟩
    by_cases hx : a = x
    · subst a
      simp only [List.count_cons, List.countP_cons, decide_true, Nat.cast_add, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ih]
    · have h_neq : decide (a = x) = false := by simp [hx]
      calc
        (∑ y : β, (List.count (x, y) ((a, b) :: L') : ℤ))
            = (∑ y : β, (List.count (x, y) L' : ℤ)) := by
          refine Finset.sum_congr rfl (λ y hy => ?_)
          simp [hx]
        _ = (List.countP (λ p : S × β => decide (p.1 = x)) L' : ℤ) := ih
        _ = (List.countP (λ p : S × β => decide (p.1 = x)) ((a, b) :: L') : ℤ) := by
          simp [h_neq]

/-! ### Lemmas bridging `countTransitionInPath` and `countAsFirst`/`countAsSecond` -/

theorem sum_countTransitionInPath_snd_eq_countAsSecond (zs : List S) (x : S) :
    (∑ y : S, (countTransitionInPath (y, x) zs : ℤ)) = (countAsSecond zs x : ℤ) := by
  simp only [countTransitionInPath, countAsSecond]
  have h := sum_count_by_snd (zs.zip zs.tail) x
  simpa using h

theorem sum_countTransitionInPath_fst_eq_countAsFirst (zs : List S) (x : S) :
    (∑ y : S, (countTransitionInPath (x, y) zs : ℤ)) = (countAsFirst zs x : ℤ) := by
  simp only [countTransitionInPath, countAsFirst]
  have h := sum_count_by_fst (zs.zip zs.tail) x
  simpa using h

theorem countAsSecond_sub_countAsFirst (zs : List S) (x : S) :
    (countAsSecond zs x : ℤ) - (countAsFirst zs x : ℤ) =
    ((if zs.getLast? = some x then 1 else 0 : ℕ) : ℤ) - ((if zs.head? = some x then 1 else 0 : ℕ) : ℤ) := by
  induction zs with
  | nil => simp [countAsSecond, countAsFirst]
  | cons a as ih =>
    cases as with
    | nil => simp [countAsSecond, countAsFirst]
    | cons b bs =>
      have h_second : (countAsSecond (a :: b :: bs) x : ℤ) =
          (if b = x then 1 else 0 : ℤ) + (countAsSecond (b :: bs) x : ℤ) := by
        simp [countAsSecond, List.countP_cons, add_comm]
      have h_first : (countAsFirst (a :: b :: bs) x : ℤ) =
          (if a = x then 1 else 0 : ℤ) + (countAsFirst (b :: bs) x : ℤ) := by
        simp [countAsFirst, List.countP_cons, add_comm]
      have h_getlast : (a :: b :: bs).getLast? = (b :: bs).getLast? := by simp
      have h_head : (a :: b :: bs).head? = some a := by simp
      have h_head' : (b :: bs).head? = some b := by simp
      rw [h_second, h_first, h_getlast, h_head, h_head'] at *
      have h_split : ((if b = x then 1 else 0 : ℤ) + (countAsSecond (b :: bs) x : ℤ)) -
          ((if a = x then 1 else 0 : ℤ) + (countAsFirst (b :: bs) x : ℤ)) =
          ((if b = x then 1 else 0 : ℤ) - (if a = x then 1 else 0 : ℤ)) +
          ((countAsSecond (b :: bs) x : ℤ) - (countAsFirst (b :: bs) x : ℤ)) := by
        omega
      rw [h_split, ih]
      simp

theorem countAsFirst_eq_countAsSecond_of_head_eq_getLast (zs : List S) (x : S)
    (h_eq : zs.head? = zs.getLast?) : countAsFirst zs x = countAsSecond zs x := by
  have h := countAsSecond_sub_countAsFirst zs x
  rw [h_eq] at h
  have hsub : ((if zs.getLast? = some x then 1 else 0 : ℕ) : ℤ) -
      ((if zs.getLast? = some x then 1 else 0 : ℕ) : ℤ) = 0 := by simp
  rw [hsub] at h
  have h_int : (countAsSecond zs x : ℤ) = (countAsFirst zs x : ℤ) := by
    omega
  exact_mod_cast h_int.symm

theorem sum_countTransitionInPath_snd_eq_sum_countTransitionInPath_fst_of_cycle
    (zs : List S) (h_eq : zs.head? = zs.getLast?) (x : S) :
    (∑ y : S, (countTransitionInPath (y, x) zs : ℤ)) = (∑ y : S, (countTransitionInPath (x, y) zs : ℤ)) := by
  calc
    (∑ y : S, (countTransitionInPath (y, x) zs : ℤ)) = (countAsSecond zs x : ℤ) :=
      sum_countTransitionInPath_snd_eq_countAsSecond zs x
    _ = (countAsFirst zs x : ℤ) := by
      rw [countAsFirst_eq_countAsSecond_of_head_eq_getLast zs x h_eq]
    _ = (∑ y : S, (countTransitionInPath (x, y) zs : ℤ)) := by
      rw [sum_countTransitionInPath_fst_eq_countAsFirst zs x]

/-! ### Cycle reduction lemmas -/

lemma countTransitionInPath_pos_of_length_ge_two (cycle : List S) (h_len : cycle.length ≥ 2) :
    ∃ t : Transition S, countTransitionInPath t cycle ≥ 1 := by
  have hne : cycle ≠ [] := by
    intro h; rw [h] at h_len; simp at h_len
  rcases List.exists_cons_of_ne_nil hne with ⟨a, rest, h_eq⟩
  have hrest_ne : rest ≠ [] := by
    intro h; rw [h_eq, h] at h_len; simp at h_len
  rcases List.exists_cons_of_ne_nil hrest_ne with ⟨b, rest', h_eq'⟩
  rw [h_eq, h_eq']
  refine ⟨(a, b), ?_⟩
  dsimp [countTransitionInPath]
  simp

/-- If a run `R` has a cycle, there exists a smaller run `R'` with the same net flow at every
    node, obtained by removing the cycle from `R`. -/
lemma exists_smaller_run_with_same_netFlow (R : Run S) (h_cycle : R.hasCycle) :
    ∃ (R' : Run S), (∀ x, R'.netFlow x = R.netFlow x) ∧ R'.size < R.size ∧ (∀ t, R' t ≤ R t) := by
  rcases h_cycle with ⟨cycle, h_len, h_eq, h_contains⟩
  set R' := R.removeCycle cycle with hR'
  refine ⟨R', ?_, ?_, ?_⟩
  · -- net flow equality: ∀ x, R'.netFlow x = R.netFlow x
    intro x
    dsimp [Run.netFlow, Run.removeCycle, R']
    have hsum1 := Finset.sum_nat_sub_eq_sub_sum (fun y => R (x, y))
      (fun y => countTransitionInPath (x, y) cycle) (fun y => h_contains (x, y))
    have hsum2 := Finset.sum_nat_sub_eq_sub_sum (fun y => R (y, x))
      (fun y => countTransitionInPath (y, x) cycle) (fun y => h_contains (y, x))
    simp at hsum1 hsum2
    have h_cycle_count_eq :=
      sum_countTransitionInPath_snd_eq_sum_countTransitionInPath_fst_of_cycle cycle h_eq x
    rw [hsum1, hsum2, h_cycle_count_eq]
    omega
  · -- size inequality: R'.size < R.size
    dsimp [Run.size, Run.removeCycle, R']
    have hle : ∀ t ∈ (Finset.univ : Finset (Transition S)),
        R t - countTransitionInPath t cycle ≤ R t := by
      intro t _; exact Nat.sub_le _ _
    have h_exists_lt : ∃ t ∈ (Finset.univ : Finset (Transition S)),
        R t - countTransitionInPath t cycle < R t := by
      rcases countTransitionInPath_pos_of_length_ge_two cycle h_len with ⟨t, ht⟩
      have hRpos : R t ≥ 1 := by
        have h_le := h_contains t
        omega
      refine ⟨t, Finset.mem_univ _, ?_⟩
      omega
    exact Finset.sum_lt_sum hle h_exists_lt
  · -- pointwise inequality: ∀ t, R' t ≤ R t
    intro t
    dsimp [R', Run.removeCycle]
    exact Nat.sub_le _ _

end Utils.StateTransition
