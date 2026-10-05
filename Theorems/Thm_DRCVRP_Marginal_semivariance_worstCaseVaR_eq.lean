import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 4 (Ghosal and Wiesemann 2020, §4.3, p. 725, Eq. (11)): the worst-case
value-at-risk of one customer's demand over the marginalized semivariance ambiguity set (10). -/
theorem semivariance_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σplus σminus : Fin n → ℝ) (hσplus : ∀ i, 0 < σplus i) (hσminus : ∀ i, 0 < σminus i)
    (i : Fin n) :
    worstCaseVaR (semivarianceSet qlo qhi μ σplus σminus) ε {i} =
      μ i + min (min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i)))
        (Real.sqrt (σplus i / ε))) (Real.sqrt ((1 - ε) * σminus i) / ε) := by sorry

end DRCVRP.Marginal

