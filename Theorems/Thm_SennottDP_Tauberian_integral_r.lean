import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 280, Eq. (A.26): `∫_0^1 r(x) dx = ∫_{e^{-1}}^1 dx/x = 1`. -/
theorem integral_r :
    ∫ x in (0 : ℝ)..1, r x = ∫ x in Real.exp (-1)..1, x⁻¹ ∧
      ∫ x in Real.exp (-1)..1, x⁻¹ = 1 := by sorry

end SennottDP.Tauberian
