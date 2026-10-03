import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_TandemFluidModel

namespace ProcessingNetworks.LyapunovCriteria

/-- Theorem 8.12, Dai & Harrison p. 141 (PDF p. 157): assuming the standard load condition
(1.1) holds (`lam1 < mu1` and `lam1 < mu2`, both stations' traffic intensities below `1`), the
fluid model corresponding to the tandem queueing system of Figure 1.1 is stable. -/
theorem tandem_queue_fluid_stable
    (lam1 mu1 mu2 : ℝ) (hlam1 : 0 ≤ lam1) (h1 : lam1 < mu1) (h2 : lam1 < mu2) :
    TandemFluidStable lam1 mu1 mu2 := by sorry

end ProcessingNetworks.LyapunovCriteria
