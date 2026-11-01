import Clean.Utils.OfflineMemory

set_option quotPrecheck false

open MemoryAccessList

/-!
Lemmas about offline memory consistency checking from `Clean.Utils.OfflineMemory`.
-/

/-- If two memory accesses have the same address, and are in address-timestamp ordering
    with distinct timestamps, then they are in timestamp ordering. -/
lemma timestamp_ordering_of_address_timestamp_ordering_and_timestamps_neq
    {t2 a2 r2 w2 t1 a1 r1 w1 : ℕ}
    (h_ord : address_timestamp_ordering (t2, a2, r2, w2) (t1, a1, r1, w1))
    (h_neq : timestamps_neq (t2, a2, r2, w2) (t1, a1, r1, w1))
    (h_eq_addr : a1 = a2) : timestamp_ordering (t2, a2, r2, w2) (t1, a1, r1, w1) := by
  simp only [address_timestamp_ordering, timestamps_neq, timestamp_ordering] at *
  rw [h_eq_addr] at h_ord
  simp only [↓reduceIte] at h_ord
  exact Nat.lt_of_le_of_ne h_ord (Ne.symm h_neq)

/-- In a list sorted by address-timestamp ordering (pairwise), if a head element `hd` and
    a tail element `a'` have the same address, then they are in timestamp ordering
    (provided timestamps are distinct). -/
lemma timestamp_ordering_of_address_timestamp_ordered_pairwise
    {hd : MemoryAccess} {tl : List MemoryAccess} {addr : ℕ}
    (h_forall : ∀ a', a' ∈ tl → address_timestamp_ordering hd a')
    (h_nodup_forall : ∀ a', a' ∈ tl → timestamps_neq hd a')
    (h_addr_eq : hd.2.1 = addr) (a' : MemoryAccess) (ha'_mem : a' ∈ tl)
    (ha'_addr : a'.2.1 = addr) : timestamp_ordering hd a' := by
  have h_ord := h_forall a' ha'_mem
  have h_neq := h_nodup_forall a' ha'_mem
  rcases hd with ⟨t_hd, a_hd, r_hd, w_hd⟩
  rcases a' with ⟨t_a', a_a', r_a', w_a'⟩
  have ha_eq : a_a' = a_hd := ha'_addr.trans h_addr_eq.symm
  exact timestamp_ordering_of_address_timestamp_ordering_and_timestamps_neq
    h_ord h_neq ha_eq

/-- `filterAddress` of a cons with the same address keeps the head element. -/
theorem filterAddress_cons_same (t a r w : ℕ) (tl : MemoryAccessList) :
    filterAddress ((t, a, r, w) :: tl) a = (t, a, r, w) :: filterAddress tl a := by
  simp [filterAddress]

/-!
## Basic structural lemmas about sortedness and timestamp distinctness
-/

theorem noTimestampDup_of_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h : MemoryAccessList.Notimestampdup (head :: tail)) :
    MemoryAccessList.Notimestampdup tail := by
  simp only [MemoryAccessList.Notimestampdup] at *
  exact List.Pairwise.of_cons h

theorem isAddressTimestampSorted_of_cons (head : MemoryAccess)
    (tail : MemoryAccessList) (h : MemoryAccessList.isAddressTimestampSorted (head :: tail)) :
    MemoryAccessList.isAddressTimestampSorted tail := by
  simp only [MemoryAccessList.isAddressTimestampSorted] at *
  exact List.Sorted.of_cons h

theorem isTimestampSorted_cons (head : MemoryAccess) (tail : MemoryAccessList) :
    MemoryAccessList.isTimestampSorted (head :: tail) →
    MemoryAccessList.isTimestampSorted tail := by
  simp_all only [MemoryAccessList.isTimestampSorted, List.sorted_cons, implies_true]

/-!
## Filtering lemmas
-/

theorem filterAddress_cons (head : MemoryAccess) (tail : MemoryAccessList) (addr : ℕ) :
    MemoryAccessList.filterAddress (head :: tail) addr =
    (if head.2.1 = addr then head :: MemoryAccessList.filterAddress tail addr
     else MemoryAccessList.filterAddress tail addr) := by
  obtain ⟨_t, a, _r, _w⟩ := head
  simp [MemoryAccessList.filterAddress, List.filter_cons]

lemma all_filterAddress (accesses : MemoryAccessList) (addr : ℕ) :
    (accesses.filterAddress addr).all (fun (_, addr', _, _) => addr' = addr) := by
  simp [MemoryAccessList.filterAddress, List.all_filter, List.all_eq_true]
  intro x hx
  rcases x with ⟨_, ax, _, _⟩
  by_cases h : ax = addr <;> simp [h]

/-!
## Filtering and address-sorted / strict-sorted properties
-/

/-- Filtering from an address-timestamp-sorted list with no timestamp duplicates
preserves timestamp sorting. -/
theorem filterAddress_sorted_from_addressTimestampSorted'
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isAddressTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (addr : ℕ) :
    (accesses.filterAddress addr).isTimestampSorted := by
  have h_strict := MemoryAccessList.addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup
    accesses h_sorted h_nodup
  simp only [MemoryAccessList.isAddressStrictTimestampSorted, MemoryAccessList.filterAddress,
    MemoryAccessList.isTimestampSorted] at h_strict ⊢
  induction accesses with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨t, a, r, w⟩
    have h_sorted_tail : MemoryAccessList.isAddressTimestampSorted tail :=
      isAddressTimestampSorted_of_cons (t, a, r, w) tail h_sorted
    have h_nodup_tail : MemoryAccessList.Notimestampdup tail :=
      noTimestampDup_of_cons (t, a, r, w) tail h_nodup
    have h_strict_tail := List.Sorted.of_cons h_strict
    simp only [List.filter_cons]
    split_ifs with h_addr
    · simp only [List.sorted_cons]
      constructor
      · intro z hz
        simp only [List.mem_filter] at hz
        obtain ⟨hz_mem, hz_addr⟩ := hz
        obtain ⟨t_z, a_z, r_z, w_z⟩ := z
        simp only [decide_eq_true_eq] at hz_addr
        simp only [List.sorted_cons] at h_strict
        have h_ord := h_strict.1 (t_z, a_z, r_z, w_z) hz_mem
        simp only [address_strict_timestamp_ordering] at h_ord
        simp only [decide_eq_true_eq] at h_addr
        rw [hz_addr, h_addr] at h_ord
        simp only [↓reduceIte] at h_ord
        simp only [timestamp_ordering]
        exact h_ord
      · exact ih h_sorted_tail h_nodup_tail h_strict_tail
    · exact ih h_sorted_tail h_nodup_tail h_strict_tail

/-- When the address changes at the second element of an address-timestamp-sorted list,
filtering by the first element's address on the tail returns an empty list. -/
theorem filterAddress_empty_when_address_changes
    (head : MemoryAccess) (second : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : MemoryAccessList.isAddressTimestampSorted (head :: second :: tail))
    (h_addr_ne : head.2.1 ≠ second.2.1) :
    MemoryAccessList.filterAddress (second :: tail) head.2.1 = [] := by
  obtain ⟨t1, a1, r1, w1⟩ := head
  obtain ⟨t2, a2, r2, w2⟩ := second
  simp at h_addr_ne
  simp only [MemoryAccessList.filterAddress]
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  obtain ⟨tx, ax, rx, wx⟩ := x
  intro h_eq
  rw [decide_eq_true_eq] at h_eq
  subst h_eq
  simp only [MemoryAccessList.isAddressTimestampSorted, List.sorted_cons] at h_sorted
  have h_ord_first := h_sorted.1 (t2, a2, r2, w2) (by simp)
  simp only [address_timestamp_ordering] at h_ord_first
  split_ifs at h_ord_first with h_eq_addr
  · exact h_addr_ne h_eq_addr.symm
  · cases hx with
    | head => linarith
    | tail _ hx_tail =>
      have h_sorted_tail := h_sorted.2
      have h_ord_second := h_sorted_tail.1 (tx, ax, rx, wx) hx_tail
      simp only [address_timestamp_ordering] at h_ord_second
      split_ifs at h_ord_second; linarith

/-!
## Single-address consistency lemmas
-/

theorem isConsistentSingleAddress_cons (head : MemoryAccess)
    (tail : MemoryAccessList)
    (h_sorted : MemoryAccessList.isTimestampSorted (head :: tail))
    (h_sorted' : tail.isTimestampSorted)
    (h : MemoryAccessList.isConsistentSingleAddress (head :: tail) h_sorted) :
    MemoryAccessList.isConsistentSingleAddress tail h_sorted' := by
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  cases tail with
  | nil => simp [MemoryAccessList.isConsistentSingleAddress]
  | cons head2 tail2 =>
    obtain ⟨t1, a1, r1, w1⟩ := head2
    simp_all [MemoryAccessList.isConsistentSingleAddress]

lemma isConsistentSingleAddress_singleton {t a r w : ℕ} {L : MemoryAccessList}
    (h_sorted : MemoryAccessList.isTimestampSorted L) (h_eq : L = [(t, a, r, w)])
    (h : MemoryAccessList.isConsistentSingleAddress L h_sorted) : r = 0 := by
  subst h_eq
  simpa [MemoryAccessList.isConsistentSingleAddress] using h

/-!
## Offline consistency lemmas
-/

theorem isConsistentOffline_of_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : MemoryAccessList.isAddressTimestampSorted (head :: tail))
    (h_offline : MemoryAccessList.isConsistentOffline (head :: tail) h_sorted) :
    MemoryAccessList.isConsistentOffline tail
      (isAddressTimestampSorted_of_cons head tail h_sorted) := by
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  cases tail with
  | nil => simp [MemoryAccessList.isConsistentOffline]
  | cons second tail_rest =>
    obtain ⟨t_second, a_second, r_second, w_second⟩ := second
    simp only [MemoryAccessList.isConsistentOffline] at h_offline ⊢
    exact h_offline.2

/-!
## Filtering and single-address consistency
-/

theorem isConsistentSingleAddress_filterAddress_of_cons (head : MemoryAccess)
    (tail : MemoryAccessList) (addr : ℕ)
    (h_sorted : MemoryAccessList.isTimestampSorted (head :: tail))
    (h : MemoryAccessList.isConsistentSingleAddress
         (MemoryAccessList.filterAddress (head :: tail) addr)
         (MemoryAccessList.filterAddress_sorted (head :: tail) h_sorted addr)) :
    MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress tail addr)
      (MemoryAccessList.filterAddress_sorted tail
        (isTimestampSorted_cons head tail h_sorted) addr) := by
  obtain ⟨t, a, r, w⟩ := head
  have h_sorted_tail := isTimestampSorted_cons (t, a, r, w) tail h_sorted
  simp only [MemoryAccessList.filterAddress, List.filter_cons] at h
  split_ifs at h with h_addr
  · exact isConsistentSingleAddress_cons (t, a, r, w)
      (MemoryAccessList.filterAddress tail addr) _
      (MemoryAccessList.filterAddress_sorted tail h_sorted_tail addr) h
  · exact h

theorem isConsistentSingleAddress_cons_forall (head : MemoryAccess)
    (tail : MemoryAccessList) (h_sorted : MemoryAccessList.isTimestampSorted (head :: tail)) :
    (∀ addr : ℕ,
      (MemoryAccessList.filterAddress (head :: tail) addr).isConsistentSingleAddress
        (MemoryAccessList.filterAddress_sorted (head :: tail) h_sorted addr)) →
    (∀ addr : ℕ,
      MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress tail addr)
        (MemoryAccessList.filterAddress_sorted tail
          (isTimestampSorted_cons head tail h_sorted) addr)) := by
  intro h addr'
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  simp_all [filterAddress_cons]
  specialize h addr'
  by_cases h_addr : a_head = addr'
  · subst h_addr
    have tail_sorted := isTimestampSorted_cons
      (t_head, a_head, r_head, w_head) tail h_sorted
    have filtered_tail_sorted := MemoryAccessList.filterAddress_sorted tail tail_sorted a_head
    have h_filtered_sorted : MemoryAccessList.isTimestampSorted
        ((t_head, a_head, r_head, w_head) :: MemoryAccessList.filterAddress tail a_head) := by
      have h_all := MemoryAccessList.filterAddress_sorted
        ((t_head, a_head, r_head, w_head) :: tail) h_sorted a_head
      simpa [filterAddress_cons] using h_all
    have h_cons := isConsistentSingleAddress_cons
      (t_head, a_head, r_head, w_head) (tail.filterAddress a_head)
      h_filtered_sorted filtered_tail_sorted
    apply h_cons
    simpa [filterAddress_cons] using h
  · simpa [filterAddress_cons, h_addr] using h

/-!
## Offline consistency implies per-address single-address consistency
-/

theorem isConsistentOffline_implies_single_address
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isAddressTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (h_offline : accesses.isConsistentOffline h_sorted)
    (addr : ℕ) :
    (accesses.filterAddress addr).isConsistentSingleAddress
      (filterAddress_sorted_from_addressTimestampSorted'
        accesses h_sorted h_nodup addr) := by
  induction accesses with
  | nil => simp [MemoryAccessList.filterAddress, MemoryAccessList.isConsistentSingleAddress]
  | cons head tail ih =>
    obtain ⟨t_head, a_head, r_head, w_head⟩ := head
    simp only [MemoryAccessList.filterAddress, List.filter_cons]
    split_ifs with h_addr
    · rw [decide_eq_true_eq] at h_addr
      subst h_addr
      cases tail with
      | nil =>
        simp [MemoryAccessList.isConsistentSingleAddress]
        exact h_offline
      | cons second tail_rest =>
        obtain ⟨t_second, a_second, r_second, w_second⟩ := second
        simp only [List.filter_cons]
        split_ifs with h_second_addr
        · rw [decide_eq_true_eq] at h_second_addr
          subst h_second_addr
          simp only [MemoryAccessList.isConsistentSingleAddress]
          constructor
          · simp only [MemoryAccessList.isConsistentOffline] at h_offline
            simp at h_offline
            exact h_offline.1
          · have ih_applied := ih
              (isAddressTimestampSorted_of_cons
                (t_head, a_second, r_head, w_head)
                ((t_second, a_second, r_second, w_second) :: tail_rest) h_sorted)
              (noTimestampDup_of_cons
                (t_head, a_second, r_head, w_head)
                ((t_second, a_second, r_second, w_second) :: tail_rest) h_nodup)
              (isConsistentOffline_of_cons
                (t_head, a_second, r_head, w_head)
                ((t_second, a_second, r_second, w_second) :: tail_rest) h_sorted h_offline)
            simp only [MemoryAccessList.filterAddress, List.filter_cons, decide_true] at ih_applied
            exact ih_applied
        · have h_addr_ne : ¬ (a_second = a_head) := by
            simp [decide_eq_true_eq] at h_second_addr
            exact h_second_addr
          have h_empty := filterAddress_empty_when_address_changes
            (t_head, a_head, r_head, w_head)
            (t_second, a_second, r_second, w_second) tail_rest h_sorted
            (by intro h_eq; exact h_addr_ne h_eq.symm)
          simp only [MemoryAccessList.filterAddress, List.filter_cons] at h_empty
          have h_second_ne : decide (a_second = a_head) = false := by
            exact decide_eq_false h_addr_ne
          simp [h_second_ne] at h_empty ⊢
          simp [h_empty, MemoryAccessList.isConsistentSingleAddress]
          simp only [MemoryAccessList.isConsistentOffline] at h_offline
          simp [h_addr_ne] at h_offline
          exact h_offline.1
    · apply ih
        (isAddressTimestampSorted_of_cons (t_head, a_head, r_head, w_head) tail h_sorted)
        (noTimestampDup_of_cons (t_head, a_head, r_head, w_head) tail h_nodup)
      exact isConsistentOffline_of_cons (t_head, a_head, r_head, w_head) tail h_sorted h_offline

/-!
## Forall versions for offline consistency
-/

theorem isConsistentSingleAddress_filterAddress_forall_of_cons'
    (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : MemoryAccessList.isAddressTimestampSorted (head :: tail))
    (h_nodup : MemoryAccessList.Notimestampdup (head :: tail))
    (h : ∀ addr, MemoryAccessList.isConsistentSingleAddress
         (MemoryAccessList.filterAddress (head :: tail) addr)
         (filterAddress_sorted_from_addressTimestampSorted'
           (head :: tail) h_sorted h_nodup addr)) :
    ∀ addr, MemoryAccessList.isConsistentSingleAddress
      (MemoryAccessList.filterAddress tail addr)
      (filterAddress_sorted_from_addressTimestampSorted' tail
        (isAddressTimestampSorted_of_cons head tail h_sorted)
        (noTimestampDup_of_cons head tail h_nodup) addr) := by
  intro addr
  obtain ⟨t, a, r, w⟩ := head
  have h_sorted_tail := isAddressTimestampSorted_of_cons (t, a, r, w) tail h_sorted
  have h_nodup_tail := noTimestampDup_of_cons (t, a, r, w) tail h_nodup
  have h_addr_spec := h addr
  simp only [MemoryAccessList.filterAddress, List.filter_cons] at h_addr_spec
  split_ifs at h_addr_spec with h_eq
  · exact isConsistentSingleAddress_cons (t, a, r, w)
      (MemoryAccessList.filterAddress tail addr) _
      (filterAddress_sorted_from_addressTimestampSorted' tail
        h_sorted_tail h_nodup_tail addr) h_addr_spec
  · exact h_addr_spec

/-- Offline consistency is equivalent to per-address single-address consistency. -/
theorem isConsistentOffline_iff_all_single_addresses (accesses : MemoryAccessList)
    (h_sorted : accesses.isAddressTimestampSorted)
    (h_nodup : accesses.Notimestampdup) :
    MemoryAccessList.isConsistentOffline accesses h_sorted ↔
    ∀ addr, MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr)
      (filterAddress_sorted_from_addressTimestampSorted' accesses h_sorted h_nodup addr) := by
  constructor
  · exact isConsistentOffline_implies_single_address accesses h_sorted h_nodup
  · induction accesses with
    | nil =>
      intro _
      simp [MemoryAccessList.isConsistentOffline]
    | cons head tail ih =>
      obtain ⟨t_h, a_h, r_h, w_h⟩ := head
      intro h_all
      cases tail with
      | nil =>
        simp [MemoryAccessList.isConsistentOffline]
        have h_a := h_all a_h
        simp [MemoryAccessList.filterAddress, MemoryAccessList.isConsistentSingleAddress] at h_a
        exact h_a
      | cons second tail_rest =>
        obtain ⟨t_s, a_s, r_s, w_s⟩ := second
        have h_sorted_tail : MemoryAccessList.isAddressTimestampSorted
            ((t_s, a_s, r_s, w_s) :: tail_rest) :=
          isAddressTimestampSorted_of_cons (t_h, a_h, r_h, w_h)
            ((t_s, a_s, r_s, w_s) :: tail_rest) h_sorted
        have h_nodup_tail : MemoryAccessList.Notimestampdup
            ((t_s, a_s, r_s, w_s) :: tail_rest) :=
          noTimestampDup_of_cons (t_h, a_h, r_h, w_h)
            ((t_s, a_s, r_s, w_s) :: tail_rest) h_nodup
        have h_all_tail :=
          isConsistentSingleAddress_filterAddress_forall_of_cons'
            (t_h, a_h, r_h, w_h) ((t_s, a_s, r_s, w_s) :: tail_rest) h_sorted
            h_nodup h_all
        have h_ih := ih h_sorted_tail h_nodup_tail h_all_tail
        refine ⟨?_, ?_⟩
        · by_cases h_eq : a_s = a_h
          · subst h_eq
            have h_a := h_all a_s
            simp [MemoryAccessList.filterAddress, MemoryAccessList.isConsistentSingleAddress] at h_a
            simp
            exact h_a.1
          · have h_filter_empty : MemoryAccessList.filterAddress
                ((t_s, a_s, r_s, w_s) :: tail_rest) a_h = [] :=
              filterAddress_empty_when_address_changes
                (t_h, a_h, r_h, w_h) (t_s, a_s, r_s, w_s) tail_rest
                h_sorted (Ne.symm h_eq)
            have h_fltr : MemoryAccessList.filterAddress
                ((t_h, a_h, r_h, w_h) :: (t_s, a_s, r_s, w_s) :: tail_rest) a_h =
                [(t_h, a_h, r_h, w_h)] := by
              simp [filterAddress_cons, h_filter_empty]
            have h_sorted_fltr := filterAddress_sorted_from_addressTimestampSorted'
              ((t_h, a_h, r_h, w_h) :: (t_s, a_s, r_s, w_s) :: tail_rest)
              h_sorted h_nodup a_h
            have h_result : r_h = 0 :=
              isConsistentSingleAddress_singleton h_sorted_fltr h_fltr (h_all a_h)
            simpa [if_neg h_eq] using h_result
        · convert h_ih

/-!
## The last write value is preserved by filtering
-/

theorem lastWriteValue_filter (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted) (addr : ℕ)
    (h_sorted' : (MemoryAccessList.filterAddress accesses addr).isTimestampSorted) :
    MemoryAccessList.lastWriteValue accesses h_sorted addr =
    MemoryAccessList.lastWriteValue (MemoryAccessList.filterAddress accesses addr) h_sorted' addr := by
  induction accesses with
  | nil => simp [MemoryAccessList.filterAddress, MemoryAccessList.lastWriteValue]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [MemoryAccessList.filterAddress, List.filter_cons, MemoryAccessList.lastWriteValue] at ⊢ ih
    by_cases h_addr : a = addr
    · simp_all [MemoryAccessList.lastWriteValue]
    · have h_sorted_tail : MemoryAccessList.isTimestampSorted tail :=
        isTimestampSorted_cons (t, a, r, w) tail h_sorted
      have h_sorted_tail' : (MemoryAccessList.filterAddress tail addr).isTimestampSorted :=
        MemoryAccessList.filterAddress_sorted tail h_sorted_tail addr
      specialize ih h_sorted_tail h_sorted_tail'
      simp [h_addr, ih]

/-!
## Online consistency and filtering
-/

/-- Online consistency is preserved by filtering by address. -/
theorem isConsistentOnline_filter_of_consistentOnline (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_consistent : MemoryAccessList.isConsistentOnline accesses h_sorted) (addr : ℕ) :
    MemoryAccessList.isConsistentOnline (MemoryAccessList.filterAddress accesses addr)
      (MemoryAccessList.filterAddress_sorted accesses h_sorted addr) := by
  induction accesses with
  | nil =>
    simp [MemoryAccessList.filterAddress, List.filter_nil, MemoryAccessList.isConsistentOnline]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [MemoryAccessList.filterAddress, List.filter_cons,
      MemoryAccessList.isConsistentOnline] at h_consistent ih ⊢
    have h_sorted' : MemoryAccessList.isTimestampSorted tail :=
      isTimestampSorted_cons (t, a, r, w) tail h_sorted
    by_cases h_addr : a = addr
    · subst h_addr
      specialize ih h_sorted' (And.right h_consistent)
      simp [MemoryAccessList.isConsistentOnline, ih]
      simp [h_consistent.left]
      rw [lastWriteValue_filter tail h_sorted' a
        (MemoryAccessList.filterAddress_sorted tail h_sorted' a)]
      simp [MemoryAccessList.filterAddress]
    · simp_all

/-!
## Structural lemmas about online consistency and sortedness proofs
-/

/-- `lastWriteValue` is independent of which proof of timestamp-sortedness is used. -/
lemma lastWriteValue_congr (accesses : MemoryAccessList) (h1 h2 : accesses.isTimestampSorted) (addr : ℕ) :
    MemoryAccessList.lastWriteValue accesses h1 addr = MemoryAccessList.lastWriteValue accesses h2 addr := by
  induction accesses with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨t, a, r, w⟩
      unfold MemoryAccessList.lastWriteValue
      split
      · rfl
      · apply ih

/-- In a consistent online memory access list, the read value equals the last write value at that address. -/
lemma isConsistentOnline_read_eq_lastWriteValue (t a r w : ℕ) (tl : MemoryAccessList)
    (h_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: tl))
    (h_consistent : MemoryAccessList.isConsistentOnline ((t, a, r, w) :: tl) h_sorted) :
    r = MemoryAccessList.lastWriteValue tl (List.Sorted.of_cons h_sorted) a := by
  have h := by simpa [MemoryAccessList.isConsistentOnline] using h_consistent
  exact h.1

/-- If the head of an online-consistent memory access list is consistent, then the tail is also consistent. -/
lemma isConsistentOnline_tail (t a r w : ℕ) (tl : MemoryAccessList)
    (h_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: tl))
    (h_consistent : MemoryAccessList.isConsistentOnline ((t, a, r, w) :: tl) h_sorted) :
    MemoryAccessList.isConsistentOnline tl (List.Sorted.of_cons h_sorted) := by
  have h := by simpa [MemoryAccessList.isConsistentOnline] using h_consistent
  exact h.2

/-- Online consistency is independent of which proof of timestamp-sortedness is used. -/
lemma isConsistentOnline_congr (accesses : MemoryAccessList) (h1 h2 : accesses.isTimestampSorted)
    (h_cons : MemoryAccessList.isConsistentOnline accesses h1) :
    MemoryAccessList.isConsistentOnline accesses h2 := by
  induction accesses with
  | nil =>
      simp [MemoryAccessList.isConsistentOnline]
  | cons hd tl ih =>
      rcases hd with ⟨t, a, r, w⟩
      unfold MemoryAccessList.isConsistentOnline at h_cons ⊢
      rcases h_cons with ⟨hr, hrest⟩
      have hr' : r = MemoryAccessList.lastWriteValue tl (List.Sorted.of_cons h2) a := by
        rw [lastWriteValue_congr tl (List.Sorted.of_cons h1) (List.Sorted.of_cons h2) a]
        exact hr
      refine ⟨hr', ?_⟩
      apply ih _ _ hrest

/-- If the head address does not match the filter address, the filtered tail is still timestamp-sorted. -/
lemma filterAddress_sorted_of_head_addr_ne (t a r w addr : ℕ) (tl : MemoryAccessList)
    (h_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: tl)) (h_ne : a ≠ addr) :
    (MemoryAccessList.filterAddress tl addr).isTimestampSorted := by
  have h := MemoryAccessList.filterAddress_sorted ((t, a, r, w) :: tl) h_sorted addr
  simpa [h_ne, MemoryAccessList.filterAddress, List.filter] using h

/-!
## Preservation of online consistency under filterAddress (induction step lemmas)
-/

/-- Induction step for `isConsistentOnline_filter_of_consistentOnline` when the head address
does not match the filter address. -/
lemma isConsistentOnline_filterAddress_cons_of_addr_ne (t a r w addr : ℕ) (tl : MemoryAccessList)
    (h_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: tl))
    (h_ne : a ≠ addr)
    (ih_res : MemoryAccessList.isConsistentOnline
      (MemoryAccessList.filterAddress tl addr)
      (MemoryAccessList.filterAddress_sorted tl (List.Sorted.of_cons h_sorted) addr)) :
    MemoryAccessList.isConsistentOnline
      (MemoryAccessList.filterAddress ((t, a, r, w) :: tl) addr)
      (MemoryAccessList.filterAddress_sorted ((t, a, r, w) :: tl) h_sorted addr) := by
  have h_ts_sorted_tl : MemoryAccessList.isTimestampSorted tl := List.Sorted.of_cons h_sorted
  have h_filter_sorted_cast : (MemoryAccessList.filterAddress tl addr).isTimestampSorted :=
    filterAddress_sorted_of_head_addr_ne t a r w addr tl h_sorted h_ne
  simpa [MemoryAccessList.isConsistentOnline, MemoryAccessList.filterAddress, h_ne, List.filter]
    using isConsistentOnline_congr (MemoryAccessList.filterAddress tl addr)
      (MemoryAccessList.filterAddress_sorted tl h_ts_sorted_tl addr) h_filter_sorted_cast ih_res

/-- Induction step for `isConsistentOnline_filter_of_consistentOnline` when the head address
matches the filter address. -/
lemma isConsistentOnline_filterAddress_cons_of_addr_eq (t a r w addr : ℕ) (tl : MemoryAccessList)
    (h_eq : a = addr)
    (h_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: tl))
    (h_consistent : MemoryAccessList.isConsistentOnline ((t, a, r, w) :: tl) h_sorted)
    (ih_res : MemoryAccessList.isConsistentOnline
      (MemoryAccessList.filterAddress tl addr)
      (MemoryAccessList.filterAddress_sorted tl (List.Sorted.of_cons h_sorted) addr)) :
    MemoryAccessList.isConsistentOnline
      (MemoryAccessList.filterAddress ((t, a, r, w) :: tl) addr)
      (MemoryAccessList.filterAddress_sorted ((t, a, r, w) :: tl) h_sorted addr) := by
  have h_ts_sorted_tl : MemoryAccessList.isTimestampSorted tl := List.Sorted.of_cons h_sorted
  have h_rw : r = MemoryAccessList.lastWriteValue tl h_ts_sorted_tl a :=
    isConsistentOnline_read_eq_lastWriteValue t a r w tl h_sorted h_consistent
  have hL_sorted_ih : (MemoryAccessList.filterAddress tl addr).isTimestampSorted :=
    MemoryAccessList.filterAddress_sorted tl h_ts_sorted_tl addr
  rw [h_eq] at h_rw
  have h_lwv_eq : r = MemoryAccessList.lastWriteValue (MemoryAccessList.filterAddress tl addr)
      hL_sorted_ih addr :=
    h_rw.trans (lastWriteValue_filter tl h_ts_sorted_tl addr hL_sorted_ih)
  have h_full : (MemoryAccessList.filterAddress ((t, a, r, w) :: tl) addr).isTimestampSorted :=
    MemoryAccessList.filterAddress_sorted ((t, a, r, w) :: tl) h_sorted addr
  have h_cons : List.Sorted timestamp_ordering
      ((t, a, r, w) :: MemoryAccessList.filterAddress tl addr) := by
    simpa [h_eq, MemoryAccessList.isTimestampSorted, MemoryAccessList.filterAddress, List.filter]
      using h_full
  have hL_sorted_cons : (MemoryAccessList.filterAddress tl addr).isTimestampSorted := by
    simpa [MemoryAccessList.isTimestampSorted] using List.Sorted.of_cons h_cons
  have h_cons_filter : MemoryAccessList.isConsistentOnline (MemoryAccessList.filterAddress tl addr)
      hL_sorted_cons :=
    isConsistentOnline_congr (MemoryAccessList.filterAddress tl addr) hL_sorted_ih
      hL_sorted_cons ih_res
  have h_lwv_eq_cons : r = MemoryAccessList.lastWriteValue (MemoryAccessList.filterAddress tl addr)
      hL_sorted_cons addr := by
    rw [lastWriteValue_congr (MemoryAccessList.filterAddress tl addr) hL_sorted_ih
      hL_sorted_cons addr]
    exact h_lwv_eq
  simpa [MemoryAccessList.isConsistentOnline, MemoryAccessList.filterAddress, h_eq, List.filter]
    using And.intro h_lwv_eq_cons h_cons_filter

/-- When all accesses are to the same address, online consistency ⇔ single-address consistency. -/
theorem isConsistentSingleAddress_iff (accesses : MemoryAccessList) (addr : ℕ)
    (h_sorted : accesses.isTimestampSorted)
    (h_eq : accesses.all (fun (_t, addr', _readValue, _writeValue) => addr' = addr)) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    MemoryAccessList.isConsistentSingleAddress accesses h_sorted := by
  induction accesses with
  | nil => simp [MemoryAccessList.isConsistentOnline, MemoryAccessList.isConsistentSingleAddress]
  | cons head tail ih =>
    constructor
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all [MemoryAccessList.isConsistentOnline, MemoryAccessList.isConsistentSingleAddress,
          MemoryAccessList.lastWriteValue]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [MemoryAccessList.isConsistentOnline, MemoryAccessList.isConsistentSingleAddress,
          MemoryAccessList.lastWriteValue] at h h_eq ih ⊢
        have h_sorted' : MemoryAccessList.isTimestampSorted ((t1, a1, r1, w1) :: tail2) :=
          isTimestampSorted_cons (t2, a2, r2, w2) ((t1, a1, r1, w1) :: tail2) h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [← ih]
        simp_all
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all [MemoryAccessList.isConsistentOnline, MemoryAccessList.isConsistentSingleAddress,
          MemoryAccessList.lastWriteValue]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [MemoryAccessList.isConsistentOnline, MemoryAccessList.isConsistentSingleAddress,
          MemoryAccessList.lastWriteValue] at h h_eq ih ⊢
        have h_sorted' : MemoryAccessList.isTimestampSorted ((t1, a1, r1, w1) :: tail2) :=
          isTimestampSorted_cons (t2, a2, r2, w2) ((t1, a1, r1, w1) :: tail2) h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [ih]
        simp_all

/-- Online consistency is equivalent to per-address single-address consistency. -/
theorem isConsistent_iff_all_single_address (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    (∀ addr : ℕ,
      MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr)
        (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)) := by
  constructor
  · intro h addr
    have h' := isConsistentSingleAddress_iff
      (accesses.filterAddress addr) addr (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)
      (all_filterAddress accesses addr)
    exact h'.mp (isConsistentOnline_filter_of_consistentOnline
      accesses h_sorted h addr)
  · intro h
    induction accesses with
    | nil => simp [MemoryAccessList.isConsistentOnline]
    | cons head tail ih =>
      obtain ⟨t, a, r, w⟩ := head
      have h_sorted' : MemoryAccessList.isTimestampSorted tail :=
        isTimestampSorted_cons (t, a, r, w) tail h_sorted
      specialize ih h_sorted'
      have h_tail := isConsistentSingleAddress_cons_forall
        (t, a, r, w) tail h_sorted h
      specialize ih h_tail
      simp only [MemoryAccessList.isConsistentOnline, ih, and_true]
      have h_tail_filter_sorted : (MemoryAccessList.filterAddress tail a).isTimestampSorted :=
        MemoryAccessList.filterAddress_sorted tail h_sorted' a
      have h_filtered_sorted : MemoryAccessList.isTimestampSorted
          ((t, a, r, w) :: (MemoryAccessList.filterAddress tail a)) := by
        simpa [filterAddress_cons] using
          MemoryAccessList.filterAddress_sorted ((t, a, r, w) :: tail) h_sorted a
      have h' := lastWriteValue_filter tail h_sorted' a h_tail_filter_sorted
      specialize h a
      simp [filterAddress_cons] at h
      have h_iff := isConsistentSingleAddress_iff
        ((t, a, r, w) :: MemoryAccessList.filterAddress tail a) a h_filtered_sorted
        (by
          simp [List.all_cons, all_filterAddress tail a])
      have is_consistent_online_full := (h_iff.mpr h)
      simp only [MemoryAccessList.isConsistentOnline] at is_consistent_online_full
      simp only [is_consistent_online_full.left]
      rw [eq_comm]
      apply lastWriteValue_filter

/-!
## Filtering by address commutes with addressTimestampSort
-/

theorem filterAddress_addressTimestampSort_eq' (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (addr : ℕ) :
    (accesses.filterAddress addr).isConsistentSingleAddress
      (MemoryAccessList.filterAddress_sorted accesses h_sorted addr) ↔
    (accesses.addressTimestampSort.filterAddress addr).isConsistentSingleAddress
      (filterAddress_sorted_from_addressTimestampSorted' accesses.addressTimestampSort
        (MemoryAccessList.addressTimestampSort_sorted accesses)
        (MemoryAccessList.addressTimestampSort_noTimestampDup accesses h_nodup) addr) := by
  have h_perm := MemoryAccessList.addressTimestampSort_perm accesses
  have h_filter_perm : (accesses.filterAddress addr).Perm
      (accesses.addressTimestampSort.filterAddress addr) := by
    simp only [MemoryAccessList.filterAddress]
    exact List.Perm.filter _ h_perm.symm
  have h_sorted1 := MemoryAccessList.filterAddress_sorted accesses h_sorted addr
  have h_sorted2 := filterAddress_sorted_from_addressTimestampSorted'
    accesses.addressTimestampSort
    (MemoryAccessList.addressTimestampSort_sorted accesses)
    (MemoryAccessList.addressTimestampSort_noTimestampDup accesses h_nodup) addr
  have h_eq : accesses.filterAddress addr = accesses.addressTimestampSort.filterAddress addr := by
    simp only [MemoryAccessList.isTimestampSorted] at h_sorted1 h_sorted2
    exact List.eq_of_perm_of_sorted h_filter_perm h_sorted1 h_sorted2
  simp [h_eq]

/-!
## Equivalence between online and offline consistency
-/

/-- Online consistency is equivalent to offline consistency of the addressTimestampSort. -/
theorem isConsistentOnline_iff_sorted_isConsistentOffline (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    MemoryAccessList.isConsistentOffline (MemoryAccessList.addressTimestampSort accesses)
      (MemoryAccessList.addressTimestampSort_sorted accesses) := by
  rw [isConsistent_iff_all_single_address]
  rw [isConsistentOffline_iff_all_single_addresses
    (MemoryAccessList.addressTimestampSort accesses)
    (MemoryAccessList.addressTimestampSort_sorted accesses)
    (MemoryAccessList.addressTimestampSort_noTimestampDup accesses h_nodup)]
  constructor
  · intro h addr
    rw [← filterAddress_addressTimestampSort_eq' accesses h_sorted h_nodup addr]
    exact h addr
  · intro h addr
    rw [filterAddress_addressTimestampSort_eq' accesses h_sorted h_nodup addr]
    exact h addr

/-!
## Permutation and sorting lemmas
-/

lemma noTimestampDup_of_TimestampSorted_perm {l1 l2 : MemoryAccessList}
    (h_sorted : l1.isTimestampSorted) (h_perm : l1.Perm l2) : l2.Notimestampdup := by
  have h_nodup : l1.Notimestampdup :=
    MemoryAccessList.noTimestampDup_of_TimestampSorted l1 h_sorted
  exact MemoryAccessList.noTimestampDup_perm l1 l2 h_nodup h_perm

lemma eq_of_perm_of_addressStrictTimestampSorted {l1 l2 : MemoryAccessList}
    (h_perm : l1.Perm l2) (h_sorted1 : l1.isAddressStrictTimestampSorted)
    (h_sorted2 : l2.isAddressStrictTimestampSorted) : l1 = l2 :=
  List.eq_of_perm_of_sorted h_perm h_sorted1 h_sorted2

lemma addressStrictTimestampSorted_of_TimestampSorted_perm {l1 l2 : MemoryAccessList}
    (h_l1_sorted : l1.isTimestampSorted) (h_l2_sorted : l2.isAddressTimestampSorted)
    (h_perm : l1.Perm l2) : l2.isAddressStrictTimestampSorted := by
  have h_l1_nodup : l1.Notimestampdup :=
    MemoryAccessList.noTimestampDup_of_TimestampSorted l1 h_l1_sorted
  have h_l2_nodup : l2.Notimestampdup :=
    MemoryAccessList.noTimestampDup_perm l1 l2 h_l1_nodup h_perm
  exact MemoryAccessList.addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup
    l2 h_l2_sorted h_l2_nodup

lemma eq_of_perm_of_sorted {l1 l2 l3 : MemoryAccessList}
    (h_l1_sorted: l1.isTimestampSorted)
    (h_l2_sorted : l2.isAddressTimestampSorted)
    (h_l3_sorted : l3.isAddressTimestampSorted)
    (h_perm1 : l1.Perm l2) (h_perm2 : l1.Perm l3) : l2 = l3 := by
  have l2_perm_l3 : l2.Perm l3 := List.Perm.trans (List.Perm.symm h_perm1) h_perm2
  have l2_strict_sorted : l2.isAddressStrictTimestampSorted :=
    addressStrictTimestampSorted_of_TimestampSorted_perm
      h_l1_sorted h_l2_sorted h_perm1
  have l3_strict_sorted : l3.isAddressStrictTimestampSorted :=
    addressStrictTimestampSorted_of_TimestampSorted_perm
      h_l1_sorted h_l3_sorted h_perm2
  exact List.eq_of_perm_of_sorted l2_perm_l3 l2_strict_sorted l3_strict_sorted

/-- Uniqueness: any address-timestamp-sorted permutation of a timestamp-sorted
list must equal the canonical addressTimestampSort. -/
lemma addressTimestampSort_unique (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (l : MemoryAccessList) (h_l_sorted : l.isAddressTimestampSorted)
    (h_perm : l.Perm accesses) :
    l = accesses.addressTimestampSort :=
  eq_of_perm_of_sorted h_sorted h_l_sorted
    (MemoryAccessList.addressTimestampSort_sorted accesses) h_perm.symm
    ((MemoryAccessList.addressTimestampSort_perm accesses).symm)

/-- If any address-sorted permutation of accesses is offline-consistent,
then the canonical addressTimestampSort is also offline-consistent. -/
lemma isConsistentOffline_canonical_of_addressSorted_perm_consistentOffline
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (l : MemoryAccessList) (h_l_sorted : l.isAddressTimestampSorted)
    (h_perm : l.Perm accesses)
    (h_offline : MemoryAccessList.isConsistentOffline l h_l_sorted) :
    MemoryAccessList.isConsistentOffline (MemoryAccessList.addressTimestampSort accesses)
      (MemoryAccessList.addressTimestampSort_sorted accesses) := by
  have h_eq : l = MemoryAccessList.addressTimestampSort accesses :=
    addressTimestampSort_unique accesses h_sorted l h_l_sorted h_perm
  subst h_eq
  exact h_offline

/-- Online consistency implies there exists an address-sorted permutation
that is offline-consistent (witnessed by addressTimestampSort). -/
lemma isConsistentOnline_implies_exists_AddressSortedMemoryAccessList
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (h_online : MemoryAccessList.isConsistentOnline accesses h_sorted) :
    ∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm accesses ∧
      MemoryAccessList.isConsistentOffline permuted.val permuted.property := by
  rw [isConsistentOnline_iff_sorted_isConsistentOffline
    accesses h_sorted h_nodup] at h_online
  refine ⟨⟨MemoryAccessList.addressTimestampSort accesses,
    MemoryAccessList.addressTimestampSort_sorted accesses⟩,
    MemoryAccessList.addressTimestampSort_perm accesses, h_online⟩

/-- If there exists an address-sorted permutation that is offline-consistent,
then the original list is online-consistent. -/
lemma exists_AddressSortedMemoryAccessList_implies_isConsistentOnline
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (h : ∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm accesses ∧
      MemoryAccessList.isConsistentOffline permuted.val permuted.property) :
    MemoryAccessList.isConsistentOnline accesses h_sorted := by
  rcases h with ⟨permuted, h_perm, h_offline⟩
  rcases permuted with ⟨permuted_val, permuted_sorted⟩
  have h_canonical_offline :
      MemoryAccessList.isConsistentOffline
        (MemoryAccessList.addressTimestampSort accesses)
        (MemoryAccessList.addressTimestampSort_sorted accesses) :=
    isConsistentOffline_canonical_of_addressSorted_perm_consistentOffline
      accesses h_sorted permuted_val permuted_sorted h_perm h_offline
  rw [isConsistentOnline_iff_sorted_isConsistentOffline
    accesses h_sorted h_nodup]
  exact h_canonical_offline

/-- Online consistency is equivalent to the existence of an address-sorted permutation
that is offline-consistent. -/
theorem isConsistentOnline_iff_isConsistentOffline_1
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    ∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm accesses ∧
      MemoryAccessList.isConsistentOffline permuted.val permuted.property := by
  constructor
  · exact isConsistentOnline_implies_exists_AddressSortedMemoryAccessList
      accesses h_sorted h_nodup
  · exact exists_AddressSortedMemoryAccessList_implies_isConsistentOnline
      accesses h_sorted h_nodup
