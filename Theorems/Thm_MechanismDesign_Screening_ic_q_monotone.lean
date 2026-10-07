import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.1**, p.11. If a direct mechanism is incentive-compatible, then `q` is (weakly)
increasing in `θ` on `[θ̲, θ̄]`. -/
theorem ic_q_monotone {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.q (Set.Icc θlo θhi) := by sorry

end MechanismDesign.Screening

