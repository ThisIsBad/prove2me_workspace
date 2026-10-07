import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.16 (Example 3.4, p.74): with both values uniform on `[0, 1]`, an expected
profit-maximizing mechanism exists among the well-defined, incentive-compatible and individually
rational direct mechanisms, and a mechanism of that class maximizes expected profit `E[t_B − t_S]`
in it if and only if, almost surely, trade takes place exactly when `θ_B − θ_S > 1/2`. -/
theorem uniform_profit_threshold :
    (∃ m : DirectMechanism uniformEnv, m.Admissible ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible →
        m'.expectedSurplus ≤ m.expectedSurplus) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible →
          m'.expectedSurplus ≤ m.expectedSurplus) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 2 < θ.2 - θ.1 then 1 else 0) := by sorry

end MechanismDesign.BilateralTrade

