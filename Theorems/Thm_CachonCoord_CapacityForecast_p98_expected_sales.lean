import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 98, the display defining `S_θ(x)`: expected sales
`S_θ(x) = x − E[(x − D_θ)⁺]` equal `x − ∫_0^x F_θ(y) dy`. (The page writes the integration
variable as `x`.) -/
theorem p98_expected_sales (M : Model) (θ : DemandType) (x : ℝ) :
    M.S θ x = x - ∫ y in (0 : ℝ)..x, cdf (M.μ θ) y := by sorry

end CachonCoord.CapacityForecast

