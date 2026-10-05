import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 3 (Ghosal and Wiesemann 2020, §4.2, p. 725, Eq. (9)): the worst-case
value-at-risk of one customer's demand over the marginalized variance ambiguity set (8). -/
theorem variance_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (i : Fin n) :
    worstCaseVaR (varianceSet qlo qhi μ σ) ε {i} =
      μ i + min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i)))
        (Real.sqrt ((1 - ε) / ε * σ i)) := by sorry

end DRCVRP.Marginal

