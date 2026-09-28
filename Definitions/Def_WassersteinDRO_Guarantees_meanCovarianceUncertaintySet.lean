import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_psdSqrt

namespace WassersteinDRO.Guarantees

/-- The mean-covariance uncertainty set `U_ε(µ̂,Ŝ)`, Kuhn et al. 2019, p. 16, displayed
equation immediately preceding Proposition 1. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
def meanCovarianceUncertaintySet {m : ℕ} (ε : ℝ) (μhat : EuclideanSpace ℝ (Fin m))
    (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) :=
  {p | p.2.PosSemidef ∧
    ‖μhat - p.1‖ ^ 2 +
      (SigmaHat + p.2 - (2 : ℝ) • psdSqrt (psdSqrt SigmaHat * p.2 * psdSqrt SigmaHat)).trace ≤ ε ^ 2}

end WassersteinDRO.Guarantees
