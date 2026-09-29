import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_nominalRisk
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 5 (Lipschitz regularization), Kuhn et al. 2019, p. 9: the worst-case risk (6) of
any fixed loss function `ℓ ∈ L` is bounded above by the Lipschitz-regularized nominal risk,
`Rε,p(PN,ℓ) ≤ R(PN,ℓ) + ε·Lip(ℓ)`. The right-hand side is formed in `EReal`/`ENNReal` so
that a non-Lipschitz `ℓ` (`Lip(ℓ) = ∞`) makes the bound `+∞`, matching the paper's own remark
that the theorem is "trivially satisfied" in that case, rather than being ruled out.
`Ξ` is closed, the paper's own standing assumption for the whole worst-case-risk framework
(PDF p. 6: "we let `Ξ ⊆ ℝ^m` be a closed set that is known to contain the support of `P`"),
carried explicitly here since it is used silently in every theorem that consumes `Ξ`. -/
theorem lipschitz_regularization {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞcl : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN]
    (ℓ : E → ℝ) (hℓ : Integrable ℓ PN) :
    worstCaseRisk ε p Ξ PN ℓ ≤
      (nominalRisk PN ℓ : EReal) + ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.Duality
