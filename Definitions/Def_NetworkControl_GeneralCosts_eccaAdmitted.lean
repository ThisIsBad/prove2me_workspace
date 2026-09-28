import Mathlib

namespace NetworkControl.GeneralCosts

/-- The ECCA Flow Control rule, p. 114-115: "we allow the full set of new arrivals `A_i(t)` into
the queue whenever `U_i(t) ≤ V`. Else, we drop all new arrivals for queue `i` entering on that
timeslot." This is the minimizer of `[U(t)-V]·R(t)` subject to `0 ≤ R(t) ≤ A(t)`, stated directly
as the book's own if-then rule rather than as an unresolved `argmin`. -/
noncomputable def eccaAdmitted (U V A : ℝ) : ℝ :=
  if U ≤ V then A else 0

end NetworkControl.GeneralCosts
