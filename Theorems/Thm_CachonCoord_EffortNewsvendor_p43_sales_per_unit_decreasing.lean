import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- p. 43, "Given that S(q, e°)/q is decreasing in q": for every effort level `e ≥ 0`, expected
sales per unit ordered `q ↦ S(q, e)/q` is strictly decreasing on `q > 0`. -/
theorem p43_sales_per_unit_decreasing (M : Model) (e : ℝ) (he : 0 ≤ e) :
    StrictAntiOn (fun q => M.S q e / q) (Set.Ioi 0) := by sorry

end CachonCoord.EffortNewsvendor

