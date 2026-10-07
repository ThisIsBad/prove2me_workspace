import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model
import Definitions.Def_MechanismDesign_Screening_NonlinearPricing

namespace MechanismDesign.Screening

/-- **Proposition 2.6**, p.24. Suppose `F` is regular (Assumption 2.1). A quantity schedule `q`
with (i) `q(θ) = 0` whenever `ν′(0)(θ − (1 − F(θ))/f(θ)) ≤ c`, and (ii) otherwise
`ν′(q(θ))(θ − (1 − F(θ))/f(θ)) = c`, together with the payment
`t(θ) = θ ν(q(θ)) − ∫_{θ̲}^{θ} ν(q(x)) dx`, is an incentive-compatible, individually rational
direct mechanism that maximizes the seller's expected profit among all incentive-compatible,
individually rational direct mechanisms of §2.3. -/
theorem nonlinear_pricing_optimal {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (E : NonlinearEnv θhi) (hreg : IsRegular D) (m : QuantityMechanism θlo θhi)
    (hq : ∀ θ ∈ Set.Icc θlo θhi,
      (deriv E.ν 0 * virtualValuation D θ ≤ E.c → m.q θ = 0) ∧
      (E.c < deriv E.ν 0 * virtualValuation D θ →
        deriv E.ν (m.q θ) * virtualValuation D θ = E.c))
    (ht : ∀ θ ∈ Set.Icc θlo θhi, m.t θ = θ * E.ν (m.q θ) - ∫ x in θlo..θ, E.ν (m.q x)) :
    m.IsIC E ∧ m.IsIR E ∧
      ∀ m' : QuantityMechanism θlo θhi, m'.IsIC E → m'.IsIR E →
        expectedProfit D E m' ≤ expectedProfit D E m := by sorry

end MechanismDesign.Screening

