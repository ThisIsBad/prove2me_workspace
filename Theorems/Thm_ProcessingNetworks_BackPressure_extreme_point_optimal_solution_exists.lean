import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

namespace ProcessingNetworks.BackPressure

/-- Proposition 9.6, Dai & Harrison p. 170 (PDF p. 186): for each system state
`(n̂, ẑ) ∈ ℤ^J_+ × ℤ^I_+` there is an optimal solution of the back-pressure optimization problem
(9.15)-(9.17) that belongs to `E`, the set of extreme allocations. The capacity consumption
matrix is nonnegative with no zero column (Section 2.1's binary `A`), which is what makes the
allocation polytope bounded, so that the linear objective attains its maximum at an extreme
point. -/
theorem extreme_point_optimal_solution_exists
    {I J K : ℕ} (dat : SPNPlanningData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (nhat : Fin J → ℕ) (zhat : Fin I → ℕ) :
    ∃ β ∈ ExtremeAllocations dat, BPFeasible dat nhat zhat β ∧
      ∀ β', BPFeasible dat nhat zhat β' →
        p dat β' (fun i => (zhat i : ℝ)) ≤ p dat β (fun i => (zhat i : ℝ)) := by sorry

end ProcessingNetworks.BackPressure
