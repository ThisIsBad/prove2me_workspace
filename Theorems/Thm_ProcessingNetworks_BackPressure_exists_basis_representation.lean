import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork

namespace ProcessingNetworks.BackPressure

/-- Lemma 9.3, Dai & Harrison p. 165 (PDF p. 181): given that Assumption 9.1 holds, let `y > 0`
be such that `Rx = y` for at least one `x ∈ ℝ^J_+`. Then there exist a basis and a vector
`x̂ ∈ ℝ^I_+` such that `R̂x̂ = y` (9.4). -/
theorem exists_basis_representation
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (y : Fin I → ℝ) (hy : ∀ i, 0 < y i)
    (x : Fin J → ℝ) (hx : ∀ j, 0 ≤ x j) (hRx : dat.R.mulVec x = y) :
    ∃ (basis : ActivityBasis dat) (xhat : Fin I → ℝ),
      (∀ i, 0 ≤ xhat i) ∧ (basisMatrix basis).mulVec xhat = y := by sorry

end ProcessingNetworks.BackPressure
