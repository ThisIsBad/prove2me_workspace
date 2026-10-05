import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 2 (Ghosal and Wiesemann 2020, §4.1, p. 724, Eq. (7)): the worst-case
value-at-risk of one customer's demand over the marginalized first-order ambiguity set (6). -/
theorem firstOrder_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (i : Fin n) :
    worstCaseVaR (firstOrderSet qlo qhi μ σ) ε {i} =
      μ i + min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i))) (1 / (2 * ε) * σ i) := by sorry

end DRCVRP.Marginal

