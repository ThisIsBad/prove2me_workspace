import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.11 (p.62), Example 3.3 (`N = 2`, types uniform on `[0, 1]`,
`0 < c < 2`): the expected profit maximizing designer chooses the rule "produce iff
`θ_1 + θ_2 > s`" with `s = 1 + c/2`. Stated as: a profit-maximizing mechanism with this rule
exists, and every profit-maximizing mechanism uses this rule for almost every `θ`. -/
theorem uniform_profit_max_threshold (c : ℝ) (hc0 : 0 < c) (hc2 : c < 2) :
    (∃ M : DirectMechanism 2, M.IsProfitMax (uniformExample c hc0) ∧
        ∀ θ ∈ (uniformExample c hc0).typeSpace, M.q θ = thresholdRule (1 + 1 / 2 * c) θ) ∧
    ∀ M : DirectMechanism 2, M.IsProfitMax (uniformExample c hc0) →
      ∀ᵐ θ ∂(uniformExample c hc0).μ, M.q θ = thresholdRule (1 + 1 / 2 * c) θ := by sorry

end MechanismDesign.PublicGoods

