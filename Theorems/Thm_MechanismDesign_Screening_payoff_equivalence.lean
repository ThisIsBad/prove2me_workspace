import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.3 (Payoff Equivalence)**, p.12. For an incentive-compatible direct mechanism,
`u(θ) = u(θ̲) + ∫_{θ̲}^{θ} q(x) dx` for all `θ ∈ [θ̲, θ̄]`. -/
theorem payoff_equivalence {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi, m.u θ = m.u θlo + ∫ x in θlo..θ, m.q x := by sorry

end MechanismDesign.Screening

