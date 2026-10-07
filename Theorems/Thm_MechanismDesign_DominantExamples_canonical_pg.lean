import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.7, p.88. Every canonical public good mechanism is dominant strategy
incentive-compatible and ex post individually rational. Moreover, for every agent `i`,
`u_i(θ̲, θ_{-i}) = 0` for all `θ_{-i} ∈ Θ_{-i}`. -/
theorem canonical_pg {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by sorry

end MechanismDesign.DominantExamples

