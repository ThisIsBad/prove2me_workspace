import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.4 (Revenue Equivalence)**, p.13. For an incentive-compatible direct mechanism,
`t(θ) = t(θ̲) + (θ q(θ) − θ̲ q(θ̲)) − ∫_{θ̲}^{θ} q(x) dx` for all `θ ∈ [θ̲, θ̄]`. -/
theorem revenue_equivalence {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi,
      m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x := by sorry

end MechanismDesign.Screening

