import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Theorem 5.1 (p. 361). Let demand be a.e. nonnegative, let AR-m be an allocation rule whose
payoffs `P^m_n([Z], ·)` are integrable for every nonnegative profile, and let `[Z]^{m*}` be a
pure-strategy Nash equilibrium under AR-m. Then there are side payments `w_n(D⃗)` (depending on
`[Z]^{m*}` and `D⃗` only), integrable in `D⃗`, such that the rule AR-m̃,
`α^{m̃}_n([Z], D⃗) = α^m_n([Z], D⃗) + w_n(D⃗)`, has (i) exactly the same Nash equilibria as AR-m,
and (ii) at `[Z]^{m*}` allocations in the core of SAG([Z]^{m*}, D⃗) for every `D⃗`. -/
theorem side_payments_preserve_equilibrium_core {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (hD : ∀ᵐ D ∂μ, ∀ n, 0 ≤ D n)
    (α : AllocationRule N W)
    (hα : ∀ Z : Profile N W, Z.Nonneg → ∀ n, Integrable (fun D => payoff sys α Z D n) μ)
    (Zm : Profile N W) (hZm : IsNashEquilibrium sys μ α Zm) :
    ∃ w : Fin N → Demand N → ℝ, (∀ n, Integrable (w n) μ) ∧
      (∀ Z : Profile N W,
        IsNashEquilibrium sys μ (fun Z' D n => α Z' D n + w n D) Z ↔ IsNashEquilibrium sys μ α Z) ∧
      ∀ D : Demand N,
        (fun n => α Zm D n + w n D) ∈ Core Finset.univ (fun S => coalitionValue sys S Zm D) := by sorry

end DecentralizedDistribution.FirstBest
