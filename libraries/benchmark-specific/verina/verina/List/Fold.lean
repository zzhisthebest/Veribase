import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Indexed folds over lists -/

/-- Fold over a list with an explicit index counter, threading a state `σ`
through the fold. The step function receives the current index, the current
state, and the current element, returning the new state.

`foldIndexedState step xs i s` folds `step` left-to-right over `xs`, starting
with index `i` and initial state `s`. For each element `x` at position `j`,
the state is updated as `step j state x`. -/
def foldIndexedState {α σ : Type} (step : Nat → σ → α → σ) :
    List α → Nat → σ → σ
  | [], _, state => state
  | x :: xs, i, state => foldIndexedState step xs (i + 1) (step i state x)

@[simp]
theorem foldIndexedState_nil {α σ : Type} (step : Nat → σ → α → σ)
    (index : Nat) (state : σ) :
    foldIndexedState step [] index state = state :=
  rfl

@[simp]
theorem foldIndexedState_cons {α σ : Type} (step : Nat → σ → α → σ)
    (x : α) (xs : List α) (index : Nat) (state : σ) :
    foldIndexedState step (x :: xs) index state =
      foldIndexedState step xs (index + 1) (step index state x) :=
  rfl

end List

end Specific
