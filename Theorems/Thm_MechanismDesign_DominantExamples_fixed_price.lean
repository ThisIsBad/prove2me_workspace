import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.12, p.93. Suppose that the set `{θ ∈ Θ | q(θ) = 1}` is closed. A direct
bilateral trade mechanism is dominant strategy incentive-compatible, ex post individually
rational and ex post exactly budget balanced if and only if either
`q(θ) = 0` and `t_S(θ) = t_B(θ) = 0` for all `θ ∈ Θ`,
or there is a price `θ̂ ∈ ℝ` such that for all `θ = (θ_S, θ_B) ∈ Θ`:
`q(θ) = 1` and `t_S(θ) = t_B(θ) = θ̂` if `θ_S ≤ θ̂` and `θ_B ≥ θ̂`;
`q(θ) = 0` and `t_S(θ) = t_B(θ) = 0` if `θ_S > θ̂` or `θ_B < θ̂`. -/
theorem fixed_price {E : TradeSetting} (M : TradeMechanism E)
    (hclosed : IsClosed {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsExactlyBudgetBalanced) ↔
      ((∀ θ ∈ E.typeSpace, M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0) ∨
        ∃ θhat : ℝ, ∀ θ ∈ E.typeSpace,
          ((θ.1 ≤ θhat ∧ θhat ≤ θ.2) → M.q θ = 1 ∧ M.tS θ = θhat ∧ M.tB θ = θhat) ∧
          ((θhat < θ.1 ∨ θ.2 < θhat) → M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0)) := by sorry

end MechanismDesign.DominantExamples

