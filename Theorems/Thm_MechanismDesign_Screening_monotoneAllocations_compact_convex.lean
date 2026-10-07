import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Lemma 2.6**, p.16. The set `M` of increasing functions `[θ̲, θ̄] → [0, 1]`, as a subset of
`F = L¹([θ̲, θ̄])` with the `L¹` norm, is compact and convex. -/
theorem monotoneAllocations_compact_convex {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi) :
    IsCompact (monotoneAllocations θlo θhi) ∧ Convex ℝ (monotoneAllocations θlo θhi) := by sorry

end MechanismDesign.Screening

