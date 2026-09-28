import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Fixed

/-- Eq. (4), the prox-inequality: for a proper convex lsc `g : E → (-∞, +∞]`,
`x̄ = prox_g z ⇔ ⟪x̄ - z, x - x̄⟫ ≥ g(x̄) - g(x)` for all `x ∈ E`. -/
theorem prox_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (hg : IsProperConvexLSC g) (z xbar : E) :
    GoldenRatioVI.Shared.IsProxPoint g z xbar ↔
      ∀ x : E, ((inner ℝ (xbar - z) (x - xbar) : ℝ) : EReal) ≥ g xbar - g x := by sorry

end GoldenRatioVI.Fixed

