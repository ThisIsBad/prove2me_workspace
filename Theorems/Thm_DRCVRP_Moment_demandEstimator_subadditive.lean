import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Moment_AmbiguitySet

open MeasureTheory

namespace DRCVRP.Moment

theorem demandEstimator_subadditive {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε Q : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hQ : 0 < Q)
    (S T : Finset (Fin n)) :
    demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q (S ∪ T) ≤
      demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q S +
        demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q T := by sorry

end DRCVRP.Moment

