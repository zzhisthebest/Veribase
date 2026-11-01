import CaseStudies.Velvet.VelvetExamples.SpMSpV_Example
import Mathlib.Tactic
import verisoftbench.Common.Array

namespace SpV

/-- The indices in a sparse vector are monotonically non-decreasing. -/
theorem ind_mono (spv : SpV α) (i j : ℕ) (hi : i < spv.size) (hj : j < spv.size) (h_le : i ≤ j) :
    spv.ind[i]! ≤ spv.ind[j]! := by
  rcases Nat.eq_or_lt_of_le h_le with (rfl | hlt)
  · rfl
  · have h_inc := spv.inc i j hi hj hlt
    omega

/-- The index array of a sparse vector is injective within bounds. -/
theorem ind_inj {α : Type} (spv : SpV α) {x y : ℕ} (hx : x < spv.size) (hy : y < spv.size)
    (h_eq : spv.ind[x]! = spv.ind[y]!) : x = y := by
  by_cases hlt : x < y
  · have h_inc := spv.inc x y hx hy hlt
    rw [h_eq] at h_inc
    omega
  · by_cases hlt' : y < x
    · have h_inc := spv.inc y x hy hx hlt'
      rw [h_eq] at h_inc
      omega
    · omega

/-- If no index in the sparse vector equals `j`, then `spv[j] = 0`. -/
theorem getElem_empty (spv : SpV Int) (j : ℕ) (h_empty : ∀ i < spv.size, spv.ind[i]! ≠ j) :
    spv[j] = 0 := by
  rcases spv.size_eq with ⟨hind_size, hval_size⟩
  have hlist_ind_len : spv.ind.toList.length = spv.size := by
    rw [Array.length_toList, hind_size]
  have hlist_val_len : spv.val.toList.length = spv.size := by
    rw [Array.length_toList, hval_size]
  let l := List.zip spv.ind.toList spv.val.toList
  have hl_len : l.length = spv.size := by
    dsimp [l]
    simp [hlist_ind_len, hlist_val_len]
  have hfind : List.find? (fun x : ℕ × ℤ => decide (x.1 = j)) l = none := by
    rw [List.find?_eq_none]
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨k, hk, hx_eq⟩
    rw [List.getElem_zip] at hx_eq
    have hx1_eq : x.1 = spv.ind.toList[k] := by
      have := Prod.mk.inj hx_eq
      exact this.1.symm
    have hk_size : k < spv.size := by
      rw [← hl_len]
      exact hk
    have hk_ind_size : k < spv.ind.size := by
      rw [hind_size]
      exact hk_size
    have h_ind_eq : spv.ind.toList[k] = spv.ind[k]! :=
      Array.toList_eq_get! spv.ind k hk_ind_size
    have hnk : spv.ind[k]! ≠ j := h_empty k hk_size
    rw [hx1_eq, h_ind_eq]
    simp [hnk]
  -- using the definition of the GetElem instance for SpV Int
  have h_matches : (List.zip spv.ind.toList spv.val.toList) = l := rfl
  have h_get : spv[j] =
      match List.find? (fun (x : ℕ × ℤ) => decide (x.1 = j)) l with
      | some pr => pr.2
      | none => 0 := by
    rfl
  rw [h_get]
  simp [hfind]

/-- When the index `j` is within bounds, the value at `spv.ind[j]!` equals `spv.val[j]!`. -/
theorem getElem_eq (spv : SpV Int) (j : ℕ) (h_ind : j < spv.size) :
    spv[spv.ind[j]!] = (spv.val)[j]! := by
  rcases spv.size_eq with ⟨hind_size, hval_size⟩
  have hi_ind : j < spv.ind.size := by rw [hind_size]; exact h_ind
  have hi_val : j < spv.val.size := by rw [hval_size]; exact h_ind
  have hlist_ind_len : spv.ind.toList.length = spv.size := by
    rw [Array.length_toList, hind_size]
  have hlist_val_len : spv.val.toList.length = spv.size := by
    rw [Array.length_toList, hval_size]
  let l := List.zip spv.ind.toList spv.val.toList
  have hl_len : l.length = spv.size := by
    dsimp [l]
    simp [hlist_ind_len, hlist_val_len]
  have hi_l : j < l.length := by
    rw [hl_len]; exact h_ind
  have hfind : List.find? (fun x : ℕ × ℤ => decide (x.1 = spv.ind[j]!)) l =
      some (spv.ind[j]!, spv.val[j]!) := by
    rw [List.find?_eq_some_iff_getElem]
    constructor
    · simp
    · refine ⟨j, hi_l, ?_, ?_⟩
      · dsimp [l]
        have h_zip_len : (List.zip spv.ind.toList spv.val.toList).length = spv.size := by
          simp [hlist_ind_len, hlist_val_len]
        have hi_zip : j < (List.zip spv.ind.toList spv.val.toList).length := by
          rw [h_zip_len]; exact h_ind
        rw [List.getElem_zip]
        have hind_i : spv.ind.toList[j] = spv.ind[j]! :=
          Array.toList_eq_get! spv.ind j hi_ind
        have hval_i : spv.val.toList[j] = spv.val[j]! :=
          Array.toList_eq_get! spv.val j hi_val
        rw [hind_i, hval_i]
      · intro k hk
        have hk_size : k < spv.size := by omega
        have h_inc := spv.inc k j hk_size h_ind hk
        have hk_ind : k < spv.ind.size := by rw [hind_size]; exact hk_size
        have h_zip_len' : (List.zip spv.ind.toList spv.val.toList).length = spv.size := by
          simp [hlist_ind_len, hlist_val_len]
        have hk_zip : k < (List.zip spv.ind.toList spv.val.toList).length := by
          rw [h_zip_len']; exact hk_size
        rw [List.getElem_zip]
        have hind_k : spv.ind.toList[k] = spv.ind[k]! :=
          Array.toList_eq_get! spv.ind k hk_ind
        rw [hind_k]
        simp
        omega
  -- using the definition of the GetElem instance for SpV Int
  have h_get : spv[spv.ind[j]!] =
      match List.find? (fun (x : ℕ × ℤ) => decide (x.1 = spv.ind[j]!)) l with
      | some pr => pr.2
      | none => 0 := by
    rfl
  rw [h_get]
  simp [hfind]

/-- General lemma relating `spv_dot` over sparse vectors to a sum over `Finset.range n`. -/
theorem dot_pure_gen (spv1 spv2 : SpV Int) (n pnt1 pnt2 : ℕ)
    (sz1 : ∀ i < spv1.size, spv1.ind[i]! < n)
    (sz2 : ∀ i < spv2.size, spv2.ind[i]! < n) :
    spv_dot spv1 spv2 pnt1 pnt2 =
    ∑ i ∈ Finset.range n,
      if max
        (if spv1.size ≤ pnt1 then n else spv1.ind[pnt1]!)
        (if spv2.size ≤ pnt2 then n else spv2.ind[pnt2]!) ≤ i then
        spv1[i] * spv2[i]
      else
        0 := by
  let cutoff (s : SpV Int) (n p : ℕ) :=
    if s.size ≤ p then n else s.ind[p]!
  have cutoff_step (s : SpV Int) (n p i : ℕ)
      (hp : p < s.size) (hi : i < n) (hnz : s[i] ≠ 0) :
      cutoff s n p ≤ i ↔ s.ind[p]! = i ∨ cutoff s n (p+1) ≤ i := by
    have hex : ∃ k, k < s.size ∧ s.ind[k]! = i := by
      by_contra h
      push_neg at h
      exact hnz (getElem_empty s i h)
    obtain ⟨k, hk, heq⟩ := hex
    simp only [cutoff, show ¬s.size ≤ p from by omega, if_false]
    by_cases hnext : s.size ≤ p+1
    · simp only [hnext, if_true]
      have hkp : k ≤ p := by omega
      by_cases hke : k = p
      · subst k; simp [heq]
      · have hinc := s.inc k p hk hp (by omega)
        omega
    · simp only [hnext, if_false]
      by_cases hkp : k < p
      · have hinc := s.inc k p hk hp hkp
        have hinc' := s.inc k (p+1) hk (by omega) (by omega)
        omega
      · by_cases hke : k = p
        · subst k; simp [heq]
        · have hm := ind_mono s (p+1) k (by omega) hk (by omega)
          have hinc := s.inc p k hp hk (by omega)
          omega
  have cutoff_next_gt (s : SpV Int) (n p : ℕ)
      (hp : p < s.size) (sz : ∀ i < s.size, s.ind[i]! < n) :
      s.ind[p]! < cutoff s n (p+1) := by
    unfold cutoff
    split
    · exact sz p hp
    · exact s.inc p (p+1) hp (by omega) (by omega)
  change spv_dot spv1 spv2 pnt1 pnt2 =
    ∑ i ∈ Finset.range n, if max (cutoff spv1 n pnt1) (cutoff spv2 n pnt2) ≤ i
      then spv1[i] * spv2[i] else 0
  induction pnt1, pnt2 using spv_dot.induct spv1 spv2 with
  | case1 p q hout =>
    rw [spv_dot, if_pos hout]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases hout with h | h <;> simp [cutoff, h, max_le_iff, show ¬n ≤ i from by omega]
  | case2 p q hout heq ih =>
    have hp : p < spv1.size := by omega
    have hq : q < spv2.size := by omega
    rw [spv_dot, if_neg hout, if_pos heq, ih]
    have hpoint : ∀ i ∈ Finset.range n,
        (if max (cutoff spv1 n p) (cutoff spv2 n q) ≤ i then spv1[i]*spv2[i] else 0) =
        (if i = spv1.ind[p]! then spv1.val[p]!*spv2.val[q]! else 0) +
        (if max (cutoff spv1 n (p+1)) (cutoff spv2 n (q+1)) ≤ i then spv1[i]*spv2[i] else 0) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases he : i = spv1.ind[p]!
      · subst i
        have hn1 := cutoff_next_gt spv1 n p hp sz1
        have hn : ¬max (cutoff spv1 n (p+1)) (cutoff spv2 n (q+1)) ≤ spv1.ind[p]! := by omega
        rw [if_neg hn]
        have hc1 : cutoff spv1 n p = spv1.ind[p]! := by simp [cutoff, show ¬spv1.size ≤ p from by omega]
        have hc2 : cutoff spv2 n q = spv1.ind[p]! := by simp [cutoff, show ¬spv2.size ≤ q from by omega, ←heq]
        simp only [hc1, hc2, max_self, le_refl, if_true, add_zero]
        rw [getElem_eq spv1 p hp, heq, getElem_eq spv2 q hq]
      · by_cases hz1 : spv1[i] = 0
        · simp [he, hz1]
        by_cases hz2 : spv2[i] = 0
        · simp [he, hz2]
        have h1 := cutoff_step spv1 n p i hp hi' hz1
        have h2 := cutoff_step spv2 n q i hq hi' hz2
        have hne1 : spv1.ind[p]! ≠ i := Ne.symm he
        have hne2 : spv2.ind[q]! ≠ i := by simpa [←heq] using hne1
        simp only [hne1, hne2, false_or] at h1 h2
        simp only [he, if_false, zero_add, max_le_iff, h1, h2]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
    simp [sz1 p hp]
  | case3 p q hout heq hlt ih =>
    rw [spv_dot, if_neg hout, if_neg heq, if_pos hlt, ih]
    apply Finset.sum_congr rfl
    intro i hi
    have hp : p < spv1.size := by omega
    have hq : q < spv2.size := by omega
    by_cases hz : spv1[i] = 0
    · simp [hz]
    have hs := cutoff_step spv1 n p i hp (Finset.mem_range.mp hi) hz
    have hq' : cutoff spv2 n q = spv2.ind[q]! := by simp [cutoff, show ¬spv2.size ≤ q from by omega]
    have hh : max (cutoff spv1 n p) (cutoff spv2 n q) ≤ i ↔
        max (cutoff spv1 n (p+1)) (cutoff spv2 n q) ≤ i := by
      rw [max_le_iff, max_le_iff, hs, hq']; omega
    simp only [hh]
  | case4 p q hout heq hlt ih =>
    rw [spv_dot, if_neg hout, if_neg heq, if_neg hlt, ih]
    apply Finset.sum_congr rfl
    intro i hi
    have hp : p < spv1.size := by omega
    have hq : q < spv2.size := by omega
    by_cases hz : spv2[i] = 0
    · simp [hz]
    have hs := cutoff_step spv2 n q i hq (Finset.mem_range.mp hi) hz
    have hp' : cutoff spv1 n p = spv1.ind[p]! := by simp [cutoff, show ¬spv1.size ≤ p from by omega]
    have hh : max (cutoff spv1 n p) (cutoff spv2 n q) ≤ i ↔
        max (cutoff spv1 n p) (cutoff spv2 n (q+1)) ≤ i := by
      rw [max_le_iff, max_le_iff, hs, hp']; omega
    simp only [hh]

/-- Special case of `dot_pure_gen` when both pointers start at 0:
    `spv_dot spv1 spv2 0 0 = ∑ i ∈ Finset.range n, spv1[i] * spv2[i]`. -/
theorem dot_pure_one (spv1 spv2 : SpV Int) (n : ℕ)
    (sz1 : ∀ i < spv1.size, spv1.ind[i]! < n) (sz2 : ∀ i < spv2.size, spv2.ind[i]! < n) :
    spv_dot spv1 spv2 0 0 = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
  rw [dot_pure_gen spv1 spv2 n 0 0 sz1 sz2]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : max (if spv1.size ≤ 0 then n else spv1.ind[0]!)
      (if spv2.size ≤ 0 then n else spv2.ind[0]!) ≤ i
  · simp only [h, if_true]
  · simp only [h, if_false]
    have zero_before (s : SpV Int)
        (hs : ¬ (if s.size ≤ 0 then n else s.ind[0]!) ≤ i) : s[i] = 0 := by
      apply getElem_empty
      intro k hk heq
      have hsize : ¬ s.size ≤ 0 := by omega
      simp only [hsize, if_false] at hs
      have hm := ind_mono s 0 k (by omega) hk (Nat.zero_le k)
      omega
    simp only [max_le_iff, not_and_or] at h
    rcases h with h | h
    · rw [zero_before spv1 h, zero_mul]
    · rw [zero_before spv2 h, mul_zero]

/-- `sumUpTo` over the full sparse vector equals the dense dot product sum. -/
theorem sumUpTo_eq_dense_sum (spv : SpV Int) (arr : Array Int) :
    sumUpTo spv arr spv.size = ∑ i ∈ Finset.range (arr.size), spv[i] * arr[i]! := by
  rw [sumUpTo]
  have hval : (∑ k ∈ Finset.range spv.size, (spv.val)[k]! * arr[spv.ind[k]!]!) =
      (∑ k ∈ Finset.range spv.size, spv[spv.ind[k]!] * arr[spv.ind[k]!]!) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < spv.size := Finset.mem_range.1 hk
    rw [getElem_eq spv k hk']
  rw [hval]
  let s := Finset.range spv.size
  let s_inbounds := Finset.filter (fun k => spv.ind[k]! < arr.size) s
  have h_split : (∑ k ∈ s, spv[spv.ind[k]!] * arr[spv.ind[k]!]!) =
      (∑ k ∈ s_inbounds, spv[spv.ind[k]!] * arr[spv.ind[k]!]!) := by
    rw [← Finset.sum_subset (Finset.filter_subset (fun k => spv.ind[k]! < arr.size) s)]
    intro k hk hk_not
    have hk_in_s : k ∈ s := hk
    have h_not_bound : ¬ (spv.ind[k]! < arr.size) := by
      intro h
      apply hk_not
      exact Finset.mem_filter.mpr ⟨hk_in_s, h⟩
    have hzero : arr[spv.ind[k]!]! = 0 := by
      simpa using (getElem!_neg arr (spv.ind[k]!) h_not_bound)
    simp [hzero]
  rw [h_split]
  have hinj : Set.InjOn (fun k => spv.ind[k]!) (s_inbounds : Set ℕ) := by
    intro x hx y hy h_eq
    have hx_lt : x < spv.size :=
      Finset.mem_range.1 ((Finset.mem_filter.1 hx).1)
    have hy_lt : y < spv.size :=
      Finset.mem_range.1 ((Finset.mem_filter.1 hy).1)
    exact ind_inj spv hx_lt hy_lt h_eq
  have himage_eq := Finset.sum_image (s := s_inbounds) (g := fun k => spv.ind[k]!)
    (f := fun i => spv[i] * arr[i]!) hinj
  have h_image : (∑ k ∈ s_inbounds, spv[spv.ind[k]!] * arr[spv.ind[k]!]!) =
      (∑ i ∈ s_inbounds.image (fun k => spv.ind[k]!), spv[i] * arr[i]!) := by
    simpa using himage_eq.symm
  rw [h_image]
  apply Finset.sum_subset
  · intro i hi
    rcases Finset.mem_image.1 hi with ⟨k, hk, rfl⟩
    have hk_bound : spv.ind[k]! < arr.size := (Finset.mem_filter.1 hk).2
    exact Finset.mem_range.2 hk_bound
  · intro i hi hi_not
    have hi_range : i < arr.size := Finset.mem_range.1 hi
    have h_no_k : ∀ k < spv.size, spv.ind[k]! ≠ i := by
      intro k hk heq
      apply hi_not
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.2 hk, ?_⟩, heq⟩
      rw [heq]
      exact hi_range
    have h_zero : spv[i] = 0 := getElem_empty spv i h_no_k
    simp [h_zero]

end SpV
