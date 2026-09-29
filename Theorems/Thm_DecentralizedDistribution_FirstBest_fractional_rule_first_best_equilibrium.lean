import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory

namespace DecentralizedDistribution.FirstBest

/-- Theorem 5.2 (p. 361), existence direction. Let `θ_n ∈ (0, 1)` with `∑_n θ_n = 1` (the paper's
`γ_n`). Under the fractional allocation rule AR-f of Eq. (11), every first-best profile
`[Z]^{c*}` (a maximizer of `J^c_𝒩` over nonnegative profiles) is a pure-strategy Nash
equilibrium (10) of the inventory game. -/
theorem fractional_rule_first_best_equilibrium {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (θ : Fin N → ℝ) (hθ : ∀ n, 0 < θ n ∧ θ n < 1) (hθsum : ∑ n, θ n = 1)
    (Zc : Profile N W) (hZc : IsFirstBest sys μ Zc) :
    IsNashEquilibrium sys μ (fractionalRule sys θ) Zc := by sorry

end DecentralizedDistribution.FirstBest
