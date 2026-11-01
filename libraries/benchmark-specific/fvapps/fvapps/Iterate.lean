namespace Specific

open _root_.List

/-! ## Fuel-bounded iteration collecting intermediate states

Iterates a step function, collecting states until a `done` condition is met
or fuel runs out.
-/

namespace Iterate

variable {α : Type _}

/-- Iterates `step` on `state` at most `fuel` times, collecting all intermediate
states **after** each step. Stops early (without collecting) when `done` is
satisfied by the current state.

Returns the empty list when `fuel = 0` or when `done` holds at the start. -/
def iterateUntilFuel (done : α → Prop) [DecidablePred done]
    (step : α → α) : Nat → α → List α
  | 0, _ => []
  | fuel + 1, state =>
      if done state then
        []
      else
        let next := step state
        next :: iterateUntilFuel done step fuel next

end Iterate

end Specific
