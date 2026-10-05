import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet

open MeasureTheory Matrix

namespace DRCVRP.Covariance

/-- Theorem 7 (p. 727): over the covariance ambiguity set (16), the worst-case value-at-risk
`sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` equals the optimal value of (17),
`maximize 1_Sᵀμ + 1_Sᵀq s.t. qᵀΣ⁻¹q ≤ (1-ε)/ε, q ∈ [q^ℓ, q^u]`. -/
theorem worstCaseVaR_eq_qcqp {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ Sig) ε S =
      sSup ((fun q : Fin n → ℝ => ∑ j ∈ S, μ j + ∑ j ∈ S, q j) ''
        {q | q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j}) := by sorry

end DRCVRP.Covariance

