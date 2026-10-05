import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.11), p. 105: the expected marginal revenue of the `S`-th seat of a
fare class, `S ≥ 1`, is `f · P[r ≥ S]`: `R̄(S) − R̄(S − 1) = EMSR(S)`, written here with
`S + 1` in place of `S` so that `S + 1 ≥ 1`. -/
theorem emsr_marginal_revenue (f : ℝ) (p : PMF ℕ) (S : ℕ) :
    expectedRevenue f p (S + 1) - expectedRevenue f p S = emsr f p (S + 1) := by sorry

end SeatInventory.Distinct

