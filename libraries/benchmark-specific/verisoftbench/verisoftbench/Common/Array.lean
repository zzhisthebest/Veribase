namespace Array

theorem toList_eq_get (a : Array α) (i : Nat) (h : i < a.size) : a.toList[i] = a[i] :=
  getElem_toList h

theorem toList_eq_get! (a : Array α) [Inhabited α] (i : Nat) (h : i < a.size) : a.toList[i] = a[i]! := by
  rw [toList_eq_get a i h]
  simp [h]

end Array
