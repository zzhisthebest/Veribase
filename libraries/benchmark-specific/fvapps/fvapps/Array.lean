import Mathlib

namespace Specific

open _root_.List

namespace Array

/-- If an element is in `mkArray n value` (an array of `n` copies of `value`),
then it must equal `value`. This is the array counterpart of `List.eq_of_mem_replicate`. -/
theorem mem_mkArray_eq {α : Type u} {n : Nat} {value x : α}
    (hx : x ∈ mkArray n value) : x = value := by
  have hxList : x ∈ (mkArray n value).toList := Array.mem_def.mp hx
  simpa [mkArray] using (List.eq_of_mem_replicate hxList)

end Array

end Specific
