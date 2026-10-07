import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.5**, p.15. If an incentive-compatible and individually rational direct mechanism
maximizes the seller's expected revenue among all incentive-compatible and individually rational
direct mechanisms, then `t(θ̲) = θ̲ q(θ̲)`. -/
theorem lowest_type_payment {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) (hir : m.IsIR)
    (hopt : ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
      expectedRevenue D m' ≤ expectedRevenue D m) :
    m.t θlo = θlo * m.q θlo := by sorry

end MechanismDesign.Screening

