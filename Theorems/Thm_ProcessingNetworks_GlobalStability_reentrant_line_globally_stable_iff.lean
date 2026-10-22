import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.25, Dai & Harrison p. 155 (PDF p. 171) — the goal theorem of this mission: the
two-station, five-class re-entrant queueing network's fluid model is globally stable if and only
if `λ1(m1+m3+m5) < 1` (8.47), `λ1(m2+m4) < 1` (8.48), and `λ1(m2+m5) < 1` (8.49). Conditions
(8.47)-(8.48) together are equivalent to the standard load condition; (8.49) is a separate
"virtual station condition," the analogue of the Rybko-Stolyar network's boundary-of-stability
requirement. -/
theorem reentrant_line_globally_stable_iff
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5) :
    FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) ↔
      (lam1 * (m1 + m3 + m5) < 1 ∧ lam1 * (m2 + m4) < 1 ∧ lam1 * (m2 + m5) < 1) := by sorry

end ProcessingNetworks.GlobalStability

