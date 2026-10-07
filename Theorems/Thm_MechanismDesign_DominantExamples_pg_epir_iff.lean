import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.6, p.87. A dominant strategy incentive-compatible direct public good
mechanism is ex post individually rational if and only if for every agent `i` and every
`θ_{-i} ∈ Θ_{-i}`: `t_i(θ̲, θ_{-i}) ≤ θ̲ q(θ̲, θ_{-i})`. -/
theorem pg_epir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q (Function.update θ i E.lo) := by sorry

end MechanismDesign.DominantExamples

