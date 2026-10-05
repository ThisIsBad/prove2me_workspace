import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.6), p. 103: for a fare class with integer requests `r` of finite mean,
expected bookings plus expected spill equal expected requests, `b̄(S) + l̄(S) = r̄`, for every
allocation `S`. -/
theorem bookings_add_spill (p : PMF ℕ) (hmean : Summable (fun r : ℕ => (p r).toReal * (r : ℝ)))
    (S : ℕ) :
    expectedBookings p S + expectedSpill p S = meanRequests p := by sorry

end SeatInventory.Distinct

