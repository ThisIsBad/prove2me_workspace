import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.2**, p.14. A direct mechanism `(q, t)` is incentive-compatible if and only if
(i) `q` is increasing on `[θ̲, θ̄]`, and (ii) for every `θ ∈ [θ̲, θ̄]`,
`t(θ) = t(θ̲) + (θ q(θ) − θ̲ q(θ̲)) − ∫_{θ̲}^{θ} q(x) dx`. -/
theorem ic_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) :
    m.IsIC ↔
      (MonotoneOn m.q (Set.Icc θlo θhi) ∧
        ∀ θ ∈ Set.Icc θlo θhi,
          m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x) := by sorry

end MechanismDesign.Screening

