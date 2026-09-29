import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Corollary 5.1 (p. 361). Let demand be a.e. nonnegative, `θ_n ∈ (0, 1)` with `∑_n θ_n = 1`,
`[Z]^{c*}` a first-best profile, and `sel` a measurable choice of optimal dual prices of (6) at
`[Z]^{c*}` for every demand realization. Under the modified fractional rule AR-c
(`α^c = α^f + w`, `w = α^d([Z]^{c*}, ·) - α^f([Z]^{c*}, ·)`): the side payments are integrable,
`[Z]^{c*}` is a pure-strategy Nash equilibrium, and at `[Z]^{c*}` the allocations are in the core
of SAG([Z]^{c*}, D⃗) for every `D⃗`. -/
theorem first_best_core_mechanism {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (hD : ∀ᵐ D ∂μ, ∀ n, 0 ≤ D n)
    (θ : Fin N → ℝ) (hθ : ∀ n, 0 < θ n ∧ θ n < 1) (hθsum : ∑ n, θ n = 1)
    (Zc : Profile N W) (hZc : IsFirstBest sys μ Zc)
    (sel : Demand N → DualPrices N W) (hsel_meas : Measurable sel)
    (hsel_opt : ∀ D, IsOptimalDual sys Zc D (sel D)) :
    (∀ n, Integrable (firstBestSidePayment sys θ Zc sel n) μ) ∧
    IsNashEquilibrium sys μ (coreFractionalRule sys θ Zc sel) Zc ∧
    ∀ D : Demand N,
      (fun n => coreFractionalRule sys θ Zc sel Zc D n)
        ∈ Core Finset.univ (fun S => coalitionValue sys S Zc D) := by sorry

end DecentralizedDistribution.FirstBest
