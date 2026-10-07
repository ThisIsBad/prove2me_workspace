import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- p. 41, the display after `Π(q, e)`: expected sales given effort `e` satisfy
`S(q, e) = q − ∫_0^q F(y|e) dy` for `q ≥ 0` and every effort level `e ≥ 0`. -/
theorem p41_expected_sales (M : Model) (q e : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e) :
    M.S q e = q - ∫ y in (0 : ℝ)..q, M.F y e := by sorry

end CachonCoord.EffortNewsvendor

