import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 6 (Robust lower bound), Kuhn et al. 2019, p. 10, eq. (9): if `PN` is the
empirical distribution of samples `ξ̂ : Fin N → E`, then the worst-case risk (6) of any fixed
loss function `ℓ ∈ L` is bounded below by the worst-case empirical loss over all perturbation
matrices `Θ = (θ_1,…,θ_N) ∈ R^{m×N}` of the training samples in an `L_{p,1}`-norm uncertainty
set, `Rε,p(PN,ℓ) ≥ sup {(1/N)Σℓ(ξ̂ᵢ+θᵢ) : θᵢ+ξ̂ᵢ ∈ Ξ ∀i, (1/N)Σ‖θᵢ‖^p ≤ εᵖ}`. The finite
supremum is cast to `EReal` (rather than left as a real `⨆`) so a constraint set with no
finite upper bound is not silently collapsed to Mathlib's real junk value `0`; `0 < N` rules
out the degenerate empty-sample case, which the paper's own indexing `i ∈ [N]` presupposes.
`Ξ` is closed, the paper's own standing assumption for the whole worst-case-risk framework
(PDF p. 6), carried explicitly since it is used silently in every theorem that consumes `Ξ`. -/
theorem robust_lower_bound {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) :
    (⨆ (θ : Fin N → E)
        (_ : ∀ i, ξhat i + θ i ∈ Ξ)
        (_ : (∑ i, ‖θ i‖ ^ p) / (N : ℝ) ≤ ε ^ p),
        (((∑ i, ℓ (ξhat i + θ i)) / (N : ℝ) : ℝ) : EReal))
      ≤ worstCaseRisk ε p Ξ (empiricalDistribution ξhat) ℓ := by sorry

end WassersteinDRO.Duality
