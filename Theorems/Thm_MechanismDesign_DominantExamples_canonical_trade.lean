import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.11, p.92. Every canonical bilateral trade mechanism is dominant strategy
incentive-compatible and ex post individually rational. Moreover, `u_S(θ̄_S, θ_B) = θ̄_S` for
every `θ_B ∈ [θ̲_B, θ̄_B]` and `u_B(θ_S, θ̲_B) = 0` for every `θ_S ∈ [θ̲_S, θ̄_S]`. -/
theorem canonical_trade {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      (∀ θB ∈ Set.Icc E.loB E.hiB, M.uS (E.hiS, θB) = E.hiS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.uB (θS, E.loB) = 0) := by sorry

end MechanismDesign.DominantExamples

