import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet
import Definitions.Def_DRCVRP_Covariance_DiagonalProgram

open MeasureTheory

namespace DRCVRP.Covariance

/-- Corollary 4 (p. 727), **corrected**. For the diagonal bound `Σ = diag(σ₁², …, σₙ²)`,
`σ_i > 0`, the worst-case value-at-risk equals the supremum of the objective of (18),
`1_Sᵀμ + ∑_{i ∈ S(θ)} q^u_i + √([(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²][∑_{i ∈ S∖S(θ)} σ_i²])`,
over the `θ ≥ 0` for which (a) the first factor under the root is nonnegative (the paper's
restriction) and (b) the induced deviations `σ_i² τ(θ)` of the customers `i ∈ S ∖ S(θ)`, where
`τ(θ) = √(slack) / √(∑_{S∖S(θ)} σ_k²)`, do not exceed `q^u_i`; (b) is written without division.
Condition (b) is the correction: as printed, without it, the claim fails already for `n = 1`,
where the supremum would be `μ₁ + σ₁√((1-ε)/ε)` even when this exceeds `q̄₁`. -/
theorem worstCaseVaR_diagonal {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hσ : ∀ i, 0 < σ i)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ (Matrix.diagonal fun i => σ i ^ 2)) ε S =
      sSup ((fun θ : ℝ => ∑ j ∈ S, μ j +
          diagObjective (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ) ''
        {θ | 0 ≤ θ ∧ 0 ≤ capSlack (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ ∧
          ∀ i ∈ S \ capSet (qUpper qlo qhi μ ε) σ S θ,
            σ i ^ 2 * Real.sqrt (capSlack (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ) ≤
              qUpper qlo qhi μ ε i *
                Real.sqrt (∑ k ∈ S \ capSet (qUpper qlo qhi μ ε) σ S θ, σ k ^ 2)}) := by sorry

end DRCVRP.Covariance

