import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist
import Definitions.Def_SennottDP_ResidualLife_Distributions

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.6, pp. 205–206: the geometric distribution `geo(μ)`
(`0 < μ < 1`), the negative binomial distribution `neg bin(μ, r)` (`0 < μ < 1`, `r ≥ 2`) and the
truncated Poisson distribution `trun Pois(λ)` (`λ > 0`) are BMRL. -/
theorem common_distributions_bmrl :
    (∀ μ : ℝ, 0 < μ → μ < 1 → IsBMRLDist (geomTrials μ)) ∧
    (∀ μ : ℝ, 0 < μ → μ < 1 → ∀ r : ℕ, 2 ≤ r → IsBMRLDist (negBinTrials μ r)) ∧
    (∀ lam : ℝ, 0 < lam → IsBMRLDist (truncPoisson lam)) := by sorry

end SennottDP.ResidualLife
