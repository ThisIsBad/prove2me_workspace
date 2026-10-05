import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Theorem 5 (§5.1, p. 726): over the first-order generic moment ambiguity set (12), the
worst-case value-at-risk of the cumulative demand of any customer subset `S` equals the optimal
value of problem (13), the infimum of its objective over `γ ∈ ℝ₊ᵖ`. -/
theorem worstCaseVaR_eq_convexProgram {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin p → Finset (Fin n)) (ν : Fin p → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      sInf (convexProgramObjective qlo qhi μ Sfam ν ε S '' {γ | ∀ l, 0 ≤ γ l}) := by sorry

end DRCVRP.FirstOrder

