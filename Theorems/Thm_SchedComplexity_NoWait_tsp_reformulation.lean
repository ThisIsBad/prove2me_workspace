import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-- The no-wait flow shop as a travelling-salesman problem (p. 24): with strictly positive
processing times, (a) some feasible no-wait schedule has `C_max ≤ y` iff some ordering `π` of
the jobs has path length `Σ_{i<n-1} c_{π i, π (i+1)} + q_{π (n-1), m} ≤ y`, and (b) some feasible
no-wait schedule has `Σ_ℓ C_ℓ ≤ y` iff some ordering `π` has
`Σ_k (Σ_{i<k} c_{π i, π (i+1)} + q_{π k, m}) ≤ y`. -/
theorem tsp_reformulation {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m)
    (hp : ∀ ℓ r, 0 < p ℓ r) (y : ℕ) :
    ((∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathMakespan p hm π ≤ (y : ℤ)) ∧
      ((∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathTotalCompletion p hm π ≤ (y : ℤ)) := by sorry

end SchedComplexity.NoWait

