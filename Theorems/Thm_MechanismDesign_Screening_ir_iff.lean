import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.3**, p.14. An incentive-compatible direct mechanism is individually rational
if and only if `u(θ̲) ≥ 0`, equivalently if and only if `t(θ̲) ≤ θ̲ q(θ̲)`. -/
theorem ir_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    (m.IsIR ↔ 0 ≤ m.u θlo) ∧ (m.IsIR ↔ m.t θlo ≤ θlo * m.q θlo) := by sorry

end MechanismDesign.Screening

