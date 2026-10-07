import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Lemma 2.7**, p.17. A function `q ∈ M` is an extreme point of `M` if and only if
`q(θ) ∈ {0, 1}` for almost all `θ ∈ [θ̲, θ̄]`. -/
theorem extremePoint_monotoneAllocations_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (g : L1Space θlo θhi) (hg : g ∈ monotoneAllocations θlo θhi) :
    IsExtremePoint (monotoneAllocations θlo θhi) g ↔
      ∀ᵐ x ∂(typeMeasure θlo θhi), (g : ℝ → ℝ) x = 0 ∨ (g : ℝ → ℝ) x = 1 := by sorry

end MechanismDesign.Screening

