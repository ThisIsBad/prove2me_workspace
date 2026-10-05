import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Theorem 3 (Ghosal and Wiesemann 2020, §4, p. 723): over every marginalized moment ambiguity
set (5), the worst-case value-at-risk of a total demand is the sum of the customers' worst-case
values-at-risk. -/
theorem worstCaseVaR_additive {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    worstCaseVaR (marginalSet qlo qhi μ φ σ) ε S =
      ∑ i ∈ S, worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} := by sorry

end DRCVRP.Marginal

