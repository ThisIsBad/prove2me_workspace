import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.10, p.91. A dominant strategy incentive-compatible direct bilateral trade
mechanism is ex post individually rational if and only if for every `θ_B ∈ [θ̲_B, θ̄_B]`,
`t_S(θ̄_S, θ_B) ≥ θ̄_S q(θ̄_S, θ_B)`, and for every `θ_S ∈ [θ̲_S, θ̄_S]`,
`t_B(θ_S, θ̲_B) ≤ θ̲_B q(θ_S, θ̲_B)`. -/
theorem trade_epir_iff {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsDSIC) :
    M.IsEPIR ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, E.hiS * M.q (E.hiS, θB) ≤ M.tS (E.hiS, θB)) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.tB (θS, E.loB) ≤ E.loB * M.q (θS, E.loB)) := by sorry

end MechanismDesign.DominantExamples

