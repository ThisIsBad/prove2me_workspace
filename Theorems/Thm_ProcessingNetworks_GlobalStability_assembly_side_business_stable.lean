import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_AssemblySideBusiness

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.21, Dai & Harrison p. 150 (PDF p. 166): for the assembly-with-side-business SPN
(Figure 5.5) under the policy "server 1 assembles whenever both buffers are non-empty; server 2
serves buffer 2 alone whenever `Z1 < Z2`," if `lam2 > lam1`, `lam1 * m1 < 1` and
`(lam2 - lam1) * m2 < 1` (Eq. 5.33), then the fluid model is stable. -/
theorem assembly_side_business_stable
    (lam1 lam2 m1 m2 : ℝ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (h1 : lam2 > lam1) (h2 : lam1 * m1 < 1) (h3 : (lam2 - lam1) * m2 < 1) :
    AssemblySideBusinessFluidStable lam1 lam2 m1 m2 := by sorry

end ProcessingNetworks.GlobalStability
