import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem virtualValuation_lt_self {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) :
    (∀ θ ∈ Set.Ico θlo θhi, virtualValuation D θ < θ) ∧ virtualValuation D θhi = θhi := by sorry

end MussaRosen.Mono

