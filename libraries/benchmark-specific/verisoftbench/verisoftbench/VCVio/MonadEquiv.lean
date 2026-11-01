import ToMathlib.Control.Monad.Equiv

set_option quotPrecheck false
universe u v w

variable {m : Type u → Type v} [Bind m] {n : Type u → Type w} [Bind n]

namespace BindEquiv

/-- `toFun` of a `BindEquiv` is injective. -/
lemma toFun_injective (f : BindEquiv m n) {α : Type u} {a b : m α}
    (h : f.toFun a = f.toFun b) : a = b := by
  calc
    a = f.invFun (f.toFun a) := by rw [f.left_inv]
    _ = f.invFun (f.toFun b) := by rw [h]
    _ = b := by rw [f.left_inv]

/-- `invFun` of a `BindEquiv` is injective. -/
lemma invFun_injective (f : BindEquiv m n) {α : Type u} {a b : n α}
    (h : f.invFun a = f.invFun b) : a = b := by
  calc
    a = f.toFun (f.invFun a) := by rw [f.right_inv]
    _ = f.toFun (f.invFun b) := by rw [h]
    _ = b := by rw [f.right_inv]

/-- `invFun` distributes over bind, i.e., `invFun` is a bind homomorphism. -/
@[simp]
lemma map_bind_inv (f : BindEquiv m n) {α β : Type u} (x : n α) (y : α → n β) :
    f.invFun (x >>= y) = f.invFun x >>= (fun a => f.invFun (y a)) := by
  refine toFun_injective f ?_
  calc
    f.toFun (f.invFun (x >>= y)) = x >>= y := f.right_inv _
    _ = (f.toFun (f.invFun x)) >>= (fun a => y a) := by rw [f.right_inv]
    _ = (f.toFun (f.invFun x)) >>= (fun a => f.toFun (f.invFun (y a))) := by
      congr; funext a; rw [f.right_inv]
    _ = f.toFun (f.invFun x >>= (fun a => f.invFun (y a))) := by rw [f.map_bind]

end BindEquiv
